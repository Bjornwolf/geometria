import Data.List
import qualified Data.Vector as V
import Graphics.UI.SDL as SDL
import Graphics.UI.SDL.Color
import Graphics.UI.SDL.Primitives
import GHC.Int

type Point = (Int, Int)
type Line = (Point, Point)
type Triangle = (Point, Point, Point)
type Edge = Int
type Edges = V.Vector Edge
type Vertex = (Triangle, Edges, Edges)
type Graph = V.Vector Vertex

-- because Data.Vector is too long
(!) = (V.!)
(//) = (V.//)

-- point operations
eq :: Point -> Point -> Bool
eq (a,b) (c,d) = a ==c && b == d

sumPoint :: Point -> Point -> Point
sumPoint (a,b) (c,d) = (a + c,b + d)

diffPoint :: Point -> Point -> Point
diffPoint (a,b) (c,d) = (a - c,b - d)

collinear :: Point -> Point -> Point -> Bool
collinear (x1,y1) (x2,y2) (x3,y3) = 
   x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2) == 0

-- vector creation
emptyGraph :: Graph
emptyGraph = V.empty

emptyEdges :: Edges
emptyEdges = V.empty

-- vertex getters
triangle :: Vertex -> Triangle
triangle (x,_,_) = x

parents :: Vertex -> Edges
parents (_,x,_) = x

children :: Vertex -> Edges
children (_,_,x) = x

-- vertex setters
swapTriangle (_,p,c) t = (t,p,c)
swapParents (t,_,c) p = (t,p,c)
swapChildren (t,p,_) c = (t,p,c)

-- graph update functions
updateTriangles :: Graph -> [(Int, Triangle)] -> Graph
updateTriangles g xs = 
   g // (map (\(x,y) -> (x, swapTriangle (g ! x) y)) xs)

updateParents :: Graph -> [(Int, Edges)] -> Graph
updateParents g xs = 
   g // (map (\(x,y) -> (x, swapParents (g ! x) y)) xs)

updateChildren :: Graph -> [(Int, Edges)] -> Graph
updateChildren g xs = 
   g // (map (\(x,y) -> (x, swapChildren (g ! x) y)) xs)

addChild :: Graph -> Int -> Edge -> Graph
addChild g n e = g // [(n, swapChildren (g ! n) (V.snoc (children (g ! n)) e))]

addParent :: Graph -> Int -> Edge -> Graph
addParent g n e = g // [(n, swapParents (g ! n) (V.snoc (parents (g ! n)) e))]

shareParents :: Graph -> Int -> Int -> Graph
shareParents g n m = 
   let newParents = joinVectors (parents (g ! n)) (parents (g ! m)) emptyEdges
   in updateParents g [(n, newParents), (m, newParents)]
   
joinVectors :: Edges -> Edges -> Edges -> Edges
joinVectors v w b =  
   if V.length v == 0 || V.length w == 0 
      then b V.++ v V.++ w 
      else if V.head v < V.head w
         then joinVectors (V.tail v) w (V.snoc b (V.head v))
         else joinVectors v (V.tail w) (V.snoc b (V.head w))

-- adding new triangles
addTriangles :: Graph -> [(Int, Triangle)] -> Graph
addTriangles g xs = foldl (\a (x,y) -> addTriangle a x y) g xs

addTriangle :: Graph -> Int -> Triangle -> Graph
addTriangle g n t = 
   addChild (V.snoc g (t, V.singleton n, emptyEdges)) n (V.length g)

-- graph deconstruction
graphToLines :: Graph -> [Line]
graphToLines g = 
   (concatMap (\x -> (triangleToLines . triangle) x) . V.toList) 
      (V.filter (\x -> (V.null . children ) x) g)

-- triangle deconstruction
triangleToLines :: Triangle -> [Line]
triangleToLines (p1,p2,p3) = [(p1,p2), (p2,p3), (p3,p1)]

-- add the point to the graph
addPoint :: Graph -> Point -> (Graph, [Line])
addPoint g p =
   let ids = nub (findTriangles g p 0) -- :: [Int]
   in let newTriangles = (map (\(x,(a,b)) -> (x,(a,b,p))) . filter (\(n,(a,b)) -> not (collinear a b p)) . concatMap (\(x,y) -> map (\z -> (x,z)) y) . (map (\(a,b) -> (a,triangleToLines b))) . (map (\x -> (x, triangle (g ! x))))) ids
      in (addTriangles g newTriangles, map (\(_,(a,b,_)) -> (a,b)) newTriangles)

findTriangles :: Graph -> Point -> Int -> [Int]
findTriangles g p n = 
   if inTriangle p (triangle (g ! n))
      then if V.null (children (g ! n))
         then [n]
         else foldl (\x y -> x ++ (findTriangles g p y)) [] ((V.toList . children) (g ! n))
      else []

inTriangle :: Point -> Triangle -> Bool
inTriangle p t = 
   let [b1, b2, b3] = (map (\(x,y) -> xProduct p x y) (triangleToLines t))
   in (b1 >= 0 && b2 >= 0 && b3 >= 0) || (b1 <= 0 && b2 <= 0 && b3 <= 0)
   where xProduct (x1,y1) (x2,y2) (x3,y3) = (x1 - x3) * (y2 - y3) - (x2 - x3) * (y1 - y3)

-- legalising edges
legaliseList :: Graph -> [(Point, (Point, Point))] -> Graph
legaliseList g [] = g
legaliseList g ((a,b):xs) = 
   let (g', xs') = legalise g a b
   in legaliseList g' (xs' ++ xs)

legalise :: Graph -> Point -> (Point, Point) -> (Graph, [(Point, (Point, Point))])
legalise g p (p1,p2) = 
   let tIDs = nub $ intersect (findTriangles g p1 0) (findTriangles g p2 0)
   in if length tIDs < 2
      then (g, [])
      else let triangles = map (\x -> triangle (g ! x)) tIDs
      in let [p3,p4] = concatMap (\(x,y,z) -> [x,y,z] \\ [p1,p2]) triangles
      in if isIllegal (p1,p2) (p3,p4)
         then let (l,newParents) = (V.length g, V.fromList tIDs)
         in let g' = V.snoc (V.snoc g ((p1,p3,p4), newParents, V.empty)) ((p2,p3,p4), newParents, V.empty)
         in (foldl (\gr (n,e) -> addChild gr n e) g' $ cartProd tIDs [l, l+1], if eq p p3 then [(p,(p2,p4)), (p,(p1,p4))] else [(p,(p2,p3)), (p,(p1,p3))])
         else (g, [])
   where cartProd xs ys = [(x,y) | x <- xs, y <- ys]

isIllegal :: (Point, Point) -> (Point, Point) -> Bool
isIllegal ((x1,y1),(x2,y2)) ((x3,y3),(x4,y4)) = 
   let {(a,b) = if detM == 0 
      then if detM' == 0
         then (div (w31 * (y2 - y3) - w23 * (y3 - y1)) detM'', div ((x3 - x1) * w23 - (x2 - x3) * w31) detM'')
         else (div (w21 * (y3 - y1) - (y2 - y1) * w31) detM', div ((x2 - x1) * w31 - (x3 - x1) * w21) detM')
      else (div (w21 * (y2 - y3) - w23 * (y2 - y1)) detM, div (w23 * (x2 - x1) - w21 * (x2 - x3)) detM)}
   in inCircle a b
   where detM = (x2 - x1) * (y2 - y3) - (x2 - x3) * (y2 - y1)
         detM' = (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)
         detM'' = (x3 - x1) * (y2 - y3) - (x2 - x3) * (y3 - y1)
         w21 = div ((x2 + x1) * (x2 - x1) + (y2 + y1) * (y2 - y1)) 2
         w23 = div ((x2 + x3) * (x2 - x3) + (y2 + y3) * (y2 - y3)) 2
         w31 = div ((x3 + x1) * (x3 - x1) + (y3 + y1) * (y3 - y1)) 2
         inCircle a b = (x3 + x4 - 2 * a) * (x4 - x3) + (y3 + y4 - 2 * b) * (y4 - y3) < 0

dispatch :: [(String, [String] -> IO ())]
dispatch = [("interactive", interactive), ("file", file)]

firstVertex :: Int -> Int -> Vertex
firstVertex x y = (((-x, 2*y), (x `div` 2, -y),(2*x, y `div` 2)), emptyEdges, emptyEdges)

interactive :: [String] -> IO ()
interactive [x', y'] = do
   let [x,y] = map read [x',y'] :: [Int]
   let graph = V.singleton $ firstVertex x y
   SDL.init [SDL.InitVideo]
   screen <- SDL.setVideoMode x y 32 [SDL.HWSurface]
   eventLoop graph screen x y

toInt16 :: Line -> ((Int16, Int16),(Int16, Int16))
toInt16 ((a,b),(c,d)) = ((intToInt16 a, intToInt16 b), (intToInt16 c, intToInt16 d))

intToInt16 :: Int -> Int16
intToInt16 x = fromIntegral (x :: Int) :: Int16

drawGraph screen _ _ [] = do
   return ()

drawGraph screen x y (((x1,y1),(x2,y2)):ps) = do
   if ok x x1 x2 && ok y y1 y2
   then do
      line screen x1 y1 x2 y2 (SDL.Pixel 0xFFFFFFFF)
      filledCircle screen x1 y1 4 (SDL.Pixel 0x0000FFFF)
      filledCircle screen x2 y2 4 (SDL.Pixel 0x0000FFFF)
      drawGraph screen x y ps
   else drawGraph screen x y ps
   where ok a b c = b > 0 && c > 0 && b < a && c < a
      

eventLoop :: Graph -> Surface -> Int -> Int -> IO ()
eventLoop g screen x y = do
   e <- waitEvent
   case e of
      Quit -> return ()
      SDL.MouseButtonDown x' y' SDL.ButtonLeft -> loop g screen x y $ pt x' y'
      otherwise -> eventLoop g screen x y
   where pt x' y' = (fromIntegral x' :: Int, fromIntegral y' :: Int)

loop g screen x y parsedPoint = do
   let g' = (\(graph, legList) -> legaliseList graph (map (\x -> (parsedPoint, x)) legList)) $ addPoint g parsedPoint
   --let g' = (\(graph, legList) -> graph) $ addPoint g parsedPoint
   SDL.fillRect screen Nothing (SDL.Pixel 0x000000)
   let linedGraph = graphToLines g'
   drawGraph screen (intToInt16 x) (intToInt16 y) $ (map toInt16 . graphToLines) g'
   SDL.flip screen
   printResult g'
   eventLoop g' screen x y


file :: [String] -> IO ()
file [fileName, x', y'] = do
   contents <- readFile fileName
   let [x,y] = map read [x',y'] :: [Int]
   let points = map (\[a,b] -> (a,b)) (map (map read . words) (lines contents))
   let graph = V.singleton $ firstVertex x y
   let graph' = foldl (\g p -> (\(g', l) -> legaliseList g' (map (\x -> (p,x)) l)) (addPoint g p)) graph points
   SDL.init [SDL.InitVideo]
   screen <- SDL.setVideoMode x y 32 [SDL.HWSurface]
   SDL.fillRect screen Nothing (SDL.Pixel 0x000000)
   drawGraph screen (intToInt16 x) (intToInt16 y) $ (map toInt16 . graphToLines) graph'
   SDL.flip screen
   printResult graph'
   eventLoop graph' screen x y
   
printResult :: Graph -> IO ()
printResult g = 
   if V.null g 
      then do
         return ()
      else do
         putStrLn $  (show . V.head) g
         printResult $ V.tail g

main :: IO ()
main = do
   (mode:args) <- getArgs
   let (Just action) = lookup mode dispatch
   action args
   

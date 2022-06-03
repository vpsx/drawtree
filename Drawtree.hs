{-
Sketching and parsing 2-D binary trees: A first Haskell project
Zoe Lynn Chitty

Introduction

    Barely five steps into writing any tree-related code in any language, one
usually feels the need to make a test tree, apply some algorithm to it, and
inspect the output. At the terminal, however, one often ends up using a 1-D
representation for the trees because it is convenient. For example, the Gentle
Introduction to Haskell [1] represents
        (Branch (Leaf 1) (Branch (Leaf 2) (Leaf 3))
        as
        <1|<2|3>>
. While easy to print and parse, this representation becomes unreadable after
very few tree layers (and the tree type used here does not even have node
values on the internal/branch nodes - only the terminal/leaf nodes.).

    I consulted some very nice resources on drawing trees [2] [3], but these
address the problem of tree _layout_ (assigning coordinates to the nodes),
ultimately drawing the trees as SVGs. I just wanted a not-so-clever 2-D ASCII
representation that I could print right to the terminal, and that ideally could
be quickly hand-written or -edited and fed directly back to a parser.

    Printing a tree in 2-D presents a particular challenge in a functional
programming context, though. Since the string is persistent, we would like to
build it left-to-right (or right-to-left); however, this imposes a traversal of
the tree that is not only breadth-first but also position-aware (that is,
needing to 'remember' not just parent-child relationships but even 'cousin'
relationships - think about placing line breaks after some groups of siblings
but not others - and to account for 'empty' nodes/non-full trees). With the
links between nodes also effectively requiring that each node's representation
be split across lines, and so forcing node representations to be interleaved
with one another (among sibling and cousin nodes), we seem to have the last
nail in the coffin of our attempt to do things recursively. (This is not to
actually declare the task impossible, but each idea I considered struck me as
seeming in some way or another to wrestle the problem awkwardly back into a
procedural paradigm.)

    In this project, I have simply skirted all these problems by
(i)  restricting the scope to binary trees, and
(ii) requiring that the representation of a tree be "full", i.e. that
     non-existent nodes be rendered - see examples below.
These two conditions ensure that all node relationships can be deduced from
positioning only, and thus rid us of the problems aforementioned - while keeping
the properties originally desired:
(1) The representation is 2-D, showing the structure of the tree in a much more
    natural and readable form than the traditional in-order one-liner; and
(2) The output from printing a tree can be fed directly back to the parser;
    the format is easy for a human to hand-write, easy for a computer to parse,
    and allows ample freedom in terms of whitespace/positioning.

EXAMPLES

    1
   / \         can be          1           will be              1
  2   3        input as      2   3         printed as         2   3
     /                      _ _ 4 _                          _ _ 4 _
    4

   'a'
   / \         can be       'a' 'b' 'c'    will be                  'a'
 'b' 'c'       input as     _ _ 'd' _      printed as         'b'         'c'
     /                                                     ___   ___   'd'   ___
   'd'

       1
      / \
     2   3     can be        1             will be                1
    /   /      input as    2         3     printed as         2       3
   4   6                  4  _      6  _                    4   _   6   _
  /   / \                8 _ _ _   1 2                     8 _ _ _ 1 2 _ _
 8   1   2


[1] https://www.haskell.org/tutorial/stdclasses.html
[2] https://crypto.stanford.edu/~blynn/haskell/drawtree.html
[3] https://llimllib.github.io/pymag-trees
-}

module Drawtree where

data Tree a = Tree {v :: a, l, r :: Maybe (Tree a)}
-- 'ScaffTrees' will be the 'faux-full' intermediate representation between
-- Trees and their string forms: non-existent nodes will be represented by
-- Nothings.
type ScaffTree a = Tree (Maybe a)


-- Some simple utility functions...

children :: [Tree a] -> [Tree a]
children xs = unMaybe (concatMap (\t -> [l t, r t]) xs)
              where unMaybe [] = []
                    unMaybe (Nothing:xs) = unMaybe xs
                    unMaybe ((Just x):xs) = x:(unMaybe xs)


depth :: Tree a -> Int
depth t = depth' [t]
          where depth' :: [Tree a] -> Int
                depth' [] = 0
                depth' xs = 1 + depth' (children xs)


-- Now we can move between Trees and ScaffTrees.


scaffold :: Tree a -> ScaffTree a
scaffold t = scaffold' ((depth t)-1) (Just t)
    where scaffold' :: Int -> Maybe (Tree a) -> ScaffTree a
          scaffold' 0 (Just (Tree v _ _)) = Tree (Just v) Nothing Nothing
          scaffold' 0 Nothing = Tree Nothing Nothing Nothing
          scaffold' d (Just (Tree v l r)) = Tree (Just v)
                                                 (Just (scaffold' (d-1) l))
                                                 (Just (scaffold' (d-1) r))
          scaffold' d Nothing = Tree Nothing
                                     (Just (scaffold' (d-1) Nothing))
                                     (Just (scaffold' (d-1) Nothing))
-- (The initial pass to find the depth of the tree is necessary because there is
-- no way for a subtree to "see" neighbouring subtrees and determine how much
-- farther down to scaffold. Still, this function is O(n).)


unscaff :: ScaffTree a -> Tree a
unscaff t = case unscaff' (Just t) of
              (Just t) -> t
              Nothing -> error "Could not unscaffold tree"
            where
            unscaff' :: Maybe (ScaffTree a) -> Maybe (Tree a)
            -- malformed trees (w/ non-Nothing children of Nothing)
            -- will be silently fixed
            unscaff' (Just (Tree Nothing _ _)) = Nothing
            unscaff' (Just (Tree (Just v) l r))
                = (Just (Tree v (unscaff' l) (unscaff' r)))
            unscaff' Nothing = Nothing


-- Next we write the parser. Thanks to the constraint that the user input
-- a 'faux-full' tree, with nonexistent nodes represented as underscores,
-- we can just parse out the whitespace to get a list of Maybe a's (let's
-- call these 'tokens'), losing no information about where each node goes.
-- The principal task is to get from this list of tokens to a ScaffTree.

-- Since our trees are persistent, it would be very inefficient to insert
-- each node into an accumulator tree; besides, inserting the nodes breadth-
-- first recursively would be unnecessarily clunky.
-- The following 'unzip' function allows us to construct the tree in one
-- recursive pass in O(n log n) time.

-- "Unzip" a list in increments of powers of 2:
-- e.g. Given some list [a,a,b,b,b,b,c,c,c,c,c,c,c,c,d,d]
-- return ([a,b,b,c,c,c,c,d,d], [a,b,b,c,c,c,c])
unzipPow2 :: [a] -> ([a], [a])
unzipPow2 xs = unzipPow2' 1 xs
    where unzipPow2' :: Int -> [a] -> ([a], [a])
          unzipPow2' _ [] = ([], [])
          unzipPow2' n xs = let one = take n xs
                                two = take n (drop n xs)
                                remaining = unzipPow2' (n*2) (drop (n*2) xs)
                            in (one++(fst remaining), two++(snd remaining))

-- "tokens-to-scaff-tree"
ttst :: [Maybe a] -> ScaffTree a
ttst xs = case ttst' xs of
             (Just t) -> t
             Nothing -> error "Could not make scafftree from tokens"
          where
          ttst' :: [Maybe a] -> Maybe (ScaffTree a)
          ttst' [] = Nothing
          ttst' (x:xs) = let unzipped = unzipPow2 xs
                         in Just (Tree x
                                       (ttst' (fst unzipped))
                                       (ttst' (snd unzipped)))


-- This done, we can finish the parser:
makeTreeFromFile :: (Read a) => FilePath -> IO (Tree a)
makeTreeFromFile f = do input <- readFile f
                        return (unscaff (ttst (makeTokens (words input))))
                     where makeTokens :: (Read a) => [String] -> [Maybe a]
                           makeTokens [] = []
                           -- (allow multiple concated underscores)
                           makeTokens (('_':_):xs) = Nothing:(makeTokens xs)
                           makeTokens (x:xs) = (Just (read x)):(makeTokens xs)


-- Usage examples:
-- (Note 1: the expected Tree type must be explicitly declared.)
-- (Note 2: in a REPL you would probably prefer <- over = so that you bind the
--          Tree and not the IO Tree. Otherwise, there is also fmap.)

mktree = makeTreeFromFile "inputTree.txt" :: IO (Tree Int)
{- Example (Tree Int): the user may input

9
8 7
66 55 __ 43
2 1 _ _ 99 99 4 3

The two illegal 99s will be removed.
Note that the user is not required to space things nicely.
-}

mktreestr = makeTreeFromFile "inputTreeString.txt" :: IO (Tree String)
{- Example (Tree String): the user may input

   "hilbert"
"vonNeumann" "curry"
_ _ "whitehead" "russell"

Note: "\n" is allowed in node values, but not actual line breaks!
-}


-- At this point we are able to go from user input to ScaffTrees to Trees,
-- and from Trees back to ScaffTrees; it only remains for us to get
-- from ScaffTrees to printable strings.


-- Node values will vary in width; align the tree according to its widest node.
maxNodeWidth :: (Show a) => Tree a -> Int
maxNodeWidth t = mnw' (Just t)
  where mnw' (Just (Tree v l r)) = maximum [length (show v), mnw' l, mnw' r]
        mnw' Nothing = 0

-- Pad input string with char until it is _at least_ int chars long.
pad :: String -> Char -> Int -> String
pad _ _ n | n < 0 = error "Cannot pad to negative length"
pad s _ 0 = s
pad (x:xs) c n = x:(pad xs c (n-1))
pad [] c n = c:(pad [] c (n-1))

-- Given list of ScaffTrees and a node width, return list of str representations
stringSTs :: (Show a) => [ScaffTree a] -> Int -> [String]
stringSTs [] _ = []
stringSTs ((Tree (Just t) _ _):xs) w = (pad (show t) ' ' w):(stringSTs xs w)
stringSTs ((Tree Nothing _ _):xs) w = (pad "_" '_' w):(stringSTs xs w)

-- Given a ScaffTree and a node width, return a string representation.
-- NB: The appropriate maxNodeWidth is that of the Tree, _not_ of the ScaffTree
-- (the ScaffTree has Nothing nodes that will be printed as _'s, not 'Nothing');
-- so the node width is determined elsewhere and passed in to this function.
scaffStr :: (Show a) => ScaffTree a -> Int -> String
scaffStr t nw = snd (scaffStr' [t] nw)
    where scaffStr' :: (Show a) => [ScaffTree a] -> Int -> (Int, String)
          scaffStr' [] _  = (0, "")
          scaffStr' xs nw
              = let (prevDepth, prevString) = scaffStr' (children xs) nw
                    d = prevDepth + 1
                    -- The spacings before and between the nodes just
                    -- grow/shrink from level to level by powers of 2
                    -- (scaled also by the node width).
                    before = (2^(d-1)-1) * nw
                    between = (2^d-1) * nw
                    row = (replicate before ' ')
                          ++ concatMap (\ x -> x ++ (replicate between ' '))
                                       (stringSTs xs nw)
                          ++ "\n"
                in (d, row ++ prevString)
-- (This function could also have been written using the `depth` function,
-- which would add in a preliminary pass; it didn't really matter either way
-- for runtime or clarity.)


-- We are now ready to write a tree-to-string function.

treeStr :: (Show a) => Tree a -> String
treeStr t = scaffStr (scaffold t) (maxNodeWidth t)

-- For convenience:

printTree :: (Show a) => Tree a -> IO ()
printTree t = do putStr (treeStr t)

printIOTree :: (Show a) => IO (Tree a) -> IO ()
printIOTree iot = do t <- iot; putStr (treeStr t)


-- And finally, we can make use of the Show class.
instance (Show a) => Show (Tree a) where show = treeStr


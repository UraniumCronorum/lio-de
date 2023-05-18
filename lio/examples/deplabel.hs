module Main where 

import LIO
import LIO.TCB
import LIO.DEPLabel

-- | Simple secrecy component example
s :: CNF
s =  ("Alice" \/ "Bob") /\  "Carla"

-- | Simple integrity component example
i :: CNF
i = "Alice" /\ "Carla"

-- | Simple label
l1 :: DCLabel
l1 = s %% i

-- | Simple label
l2 :: DCLabel
l2 = "Djon" %% "Alice"

-- | Creating privilege using constructor from TCB
p :: DCPriv
p = PrivTCB  $ "Alice" /\ "Carla"

main :: IO ()
main = do
  putStrLn $ "Label 1: " ++ show l1
  putStrLn $ "Label 2: " ++ show l2
  putStrLn $ "Join of labels: " ++ show (l1 `lub` l2)
  putStrLn $ "Meet of labels: " ++ show (l1 `glb` l2)
  putStrLn $ "Privileges: " ++ show p
  putStrLn $ "Label 1 flows to Label 2? " ++ (show $ canFlowTo l1 l2)
  putStrLn $ "Label 1 flows to Label 2 given privileges? " ++
             (show $ canFlowToP p l1 l2)
{-
Output:
ghci> main
Label 1: "Carla" /\ ("Alice" \/ "Bob") %% "Alice" /\ "Carla"
Label 2: "Djon" %% "Alice"
Join of labels: "Carla" /\ "Djon" /\ ("Alice" \/ "Bob") %% "Alice"
Meet of labels: ("Carla" \/ "Djon") /\ ("Alice" \/ "Bob" \/ "Djon") %% "Alice" /\ "Carla"
Privileges: PrivTCB ("Alice" /\ "Carla")
Label 1 flows to Label 2? False
Label 1 flows to Label 2 given privileges? True
-}

import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Basic
import OAI.LinearAlgebra.MatrixMultiplication.Numerical.AllFieldCertificatesReplay
import Std.Data.TreeMap.Basic

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters.Contractions

open MatrixMultiplication.AllFieldCertificates.Replay

abbrev Ref := Nat
abbrev Law (α : Type) := List (α × Ref)

variable {α : Type}

structure BuildState where
  reversed : List Op := []
  count : Nat := 0
  memo : Std.TreeMap (Nat × Int × Nat) Nat
    (cmp := (@lexOrd Nat (Int × Nat) inferInstance lexOrd).compare) := {}

def BuildState.program (s : BuildState) : Program := s.reversed.reverse.toArray

def opKey : Op → Nat × Int × Nat
  | .constant q => (0,q.num,q.den)
  | .add i j => (1,i,j)
  | .neg i => (2,i,0)
  | .mul i j => (3,i,j)
  | .inv i => (4,i,0)
  | .log i => (5,i,0)

abbrev Build := StateM BuildState

def emit (op : Op) : Build Ref := do
  let s ← get
  match s.memo[opKey op]? with
  | some i => pure i
  | none =>
      let i := s.count
      set ({
        reversed := op :: s.reversed
        count := i + 1
        memo := s.memo.insert (opKey op) i } : BuildState)
      pure i

def lit (q : ℚ) : Build Ref := emit (.constant q)

def add (a b : Ref) : Build Ref :=
  if a = 0 then pure b else if b = 0 then pure a else emit (.add a b)

def neg (a : Ref) : Build Ref := if a = 0 then pure a else emit (.neg a)

def sub (a b : Ref) : Build Ref := do add a (← neg b)

def mul (a b : Ref) : Build Ref :=
  if a = 0 then pure a else if b = 0 then pure b else
  if a = 1 then pure b else if b = 1 then pure a else emit (.mul a b)

def inv (a : Ref) : Build Ref := if a = 1 then pure a else emit (.inv a)

def divide (a b : Ref) : Build Ref := do mul a (← inv b)

def log (a : Ref) : Build Ref :=
  if a = 0 ∨ a = 1 then pure 0 else emit (.log a)

def powerAux (a : Ref) : Nat → Nat → Build Ref
  | 0, _ => pure 1
  | fuel + 1, n =>
      if n = 0 then pure 1 else if n = 1 then pure a else do
        let h ← powerAux a fuel (n / 2)
        let s ← mul h h
        if n % 2 = 1 then mul s a else pure s

def power (a : Ref) (n : Nat) : Build Ref := powerAux a n n

def sumRefs (xs : List Ref) : Build Ref := xs.foldlM add 0

def getLaw [BEq α] (xs : Law α) (key : α) : Ref :=
  ((xs.find? (fun x => x.1 == key)).map Prod.snd).getD 0

def addMass [BEq α] (xs : Law α) (key : α) (mass : Ref) : Build (Law α) := do
  match xs with
  | [] => pure [(key, mass)]
  | (k, v) :: rest =>
      if k == key then pure ((k, ← add v mass) :: rest)
      else pure ((k, v) :: (← addMass rest key mass))

def normalize (xs : Law α) : Build (Law α) := do
  let total ← sumRefs (xs.map Prod.snd)
  xs.mapM fun (key, mass) => do pure (key, ← divide mass total)

def entropy (xs : List Ref) : Build Ref := do
  let xs := xs.filter (· != 0)
  let total ← sumRefs xs
  sub (← mul total (← log total))
    (← sumRefs (← xs.mapM fun x => do mul x (← log x)))

def buildWeight (n : ℤ) : Build Ref := do
  let y ← divide (← lit n) (← lit 640000)
  let terms ← (List.range 17).mapM fun j => do
    divide (← power y j) (← lit (Nat.factorial j))
  power (← sumRefs terms) 64

def insertInteger (n : ℤ) : List ℤ → List ℤ
  | [] => [n]
  | m :: ms => if n ≤ m then n :: m :: ms else m :: insertInteger n ms

def sortIntegers : List ℤ → List ℤ
  | [] => []
  | n :: ns => insertInteger n (sortIntegers ns)

def weightArguments : List ℤ :=
  (sortIntegers (0 :: (tablea ++ tableP ++ tablep ++ tablez))).eraseDups

def buildWeights : Build (Law ℤ) :=
  weightArguments.mapM fun n => do pure (n, ← buildWeight n)

def initialMultiplicity (g : Shape) : Nat :=
  if g 0 = g 2 then 1 else if g 0 = g 1 ∨ g 1 = g 2 then 3 else 6

def buildInitial (weights : Law ℤ) : Build (Law Shape) := do
  let unnormalized ← sortedInitial.mapM fun g => do
    let a := getLaw weights (tablea[g 0]?.getD 0)
    let b := getLaw weights (tablea[g 1]?.getD 0)
    let c := getLaw weights (tablea[g 2]?.getD 0)
    let x ← mul a (← lit (initialMultiplicity g))
    pure (g, ← mul (← mul x b) c)
  normalize unnormalized

def buildSplit (weights : Law ℤ) (parents : List Shape) (data : List ℤ) :
    Build (List (Shape × Law Shape)) :=
  parents.mapM fun s => do
    let unnormalized ← (below s).mapM fun u => do
      let signature := splitSignature parents data s u
      let x ← mul (getLaw weights (signature 0)) (getLaw weights (signature 1))
      pure (u, ← mul x (getLaw weights (signature 2)))
    pure (s, ← normalize unnormalized)

def getSplit (laws : List (Shape × Law Shape)) (s : Shape) : Law Shape :=
  ((laws.find? (fun x => x.1 == s)).map Prod.snd).getD []

def buildBinary : Build (Law (Shape × Shape)) :=
  binaryKeys.mapM fun (t, u) => do
    pure ((t, u), ← divide (← lit (binaryInteger t u)) (← lit 1000000))

def buildZeroPairs (weights : Law ℤ) : Build (List (Shape × Law PairSlot)) :=
  zeroSecond.mapM fun t => do

    let slots := ((unorderedPairs t).flatMap fun (i,j) => [(i,j),(j,i)]).eraseDups
    let law := slots.map fun (i,j) => ((i,j), getLaw weights (orderedPairInteger t i j))
    pure (t, ← normalize law)

def getPairs (laws : List (Shape × Law PairSlot)) (s : Shape) : Law PairSlot :=
  ((laws.find? (fun x => x.1 == s)).map Prod.snd).getD []

def littleLaw (binary : Law (Shape × Shape)) (t u : Shape) (w : Fin 3) :
    Build (Law (Fin 6)) := do
  if u w = 2 then
    let d := getLaw binary (t,u)
    let c ← sub 1 d
    pure ([(2,c),(3,d)].filter (fun e => e.2 != 0))
  else
    pure [((([0,1,2,3,4,5] : List (Fin 6)).find?
      (fun i => statisticWeight i == u w)).getD 0, 1)]

def pair [BEq α] (p : Law Shape) (s : Shape) (q : List (Shape × Law α)) :
    Build (Law (α × α)) := do
  let mut result := []
  for (u, mass) in p do
    let left := ((q.find? (fun e => e.1 == u)).map Prod.snd).getD []
    let right := ((q.find? (fun e => e.1 == complement s u)).map Prod.snd).getD []
    for (i, vi) in left do
      for (j, vj) in right do
        let product ← mul (← mul mass vi) vj
        result ← addMass result (i,j) product
  pure result

def maxAxis (s : Shape) : Fin 3 :=
  (([0,1,2] : List (Fin 3)).find? (fun w => s w == shapeMax s)).getD 0

def buildHalfLaws (splits : List (Shape × Law Shape))
    (binary : Law (Shape × Shape)) (pairs : List (Shape × Law PairSlot)) :
    Build (List ((Shape × Fin 3) × Law PairSlot)) := do
  let mut result := []
  for t in shapes 8 do
    for w in ([0,1,2] : List (Fin 3)) do
      let law ← if positive t then do
        let p := getSplit splits t
        let q ← p.mapM fun (u,_) => do pure (u, ← littleLaw binary t u w)
        pair p t q
      else if t w = 0 then pure [((0,0),1)]
      else if w = maxAxis t then pure (getPairs pairs t)
      else pure ((getPairs pairs t).map fun ((i,j),mass) => ((kappa i,kappa j),mass))
      result := result ++ [((t,w),law)]
  pure result

def getHalf (laws : List ((Shape × Fin 3) × Law PairSlot)) (t : Shape) (w : Fin 3) :
    Law PairSlot :=
  ((laws.find? (fun e => e.1 == (t,w))).map Prod.snd).getD []

def orders : List (Fin 3 × Fin 3 × Fin 3) :=
  [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]

def priority (t : Shape) : Fin 3 × Fin 3 × Fin 3 :=
  (orders.find? fun (x,y,z) =>
    ([shape 1 1 6, shape 1 2 5, shape 1 3 4, shape 2 2 4, shape 3 2 3]).contains
      (shape (t x) (t y) (t z))).getD (0,1,2)

def capacity [BEq α] (s : Shape) (p : Law Shape)
    (order : Fin 3 × Fin 3 × Fin 3) (laws : Shape → Fin 3 → Build (Law α)) :
    Build (List Ref) := do
  let (x,y,z) := order
  let mut marginal := []
  for (u,mass) in p do
    marginal ← addMass marginal (u x) mass
  let first ← entropy (marginal.map Prod.snd)
  let mut result := [first]
  for w in [y,z] do
    let q ← p.mapM fun (u,_) => do pure (u, ← laws u w)
    let mut groups : List (Nat × Law α) := []
    let mut singleton := 0
    for (u,mass) in p do
      let law := ((q.find? (fun e => e.1 == u)).map Prod.snd).getD []
      let single := if w = y then u z = 0 else u x = 0 ∨ u y = 0
      if single then
        singleton ← add singleton (← mul mass (← entropy (law.map Prod.snd)))
      else
        let key := u w
        let mut group := ((groups.find? (fun e => e.1 == key)).map Prod.snd).getD []
        for (i,val) in law do
          group ← addMass group i (← mul mass val)
        if groups.any (fun e => e.1 == key) then
          groups := groups.map fun e => if e.1 == key then (key,group) else e
        else groups := groups ++ [(key,group)]
    let groupEntropies ← groups.mapM fun e => entropy (e.2.map Prod.snd)
    let j ← add singleton (← sumRefs groupEntropies)
    let joint ← pair p s q
    let cap ← sub (← entropy (joint.map Prod.snd)) (← mul j (← lit 2))
    result := result ++ [cap]
  pure result

def sortShape (t : Shape) : Shape :=
  let a := min (t 0) (min (t 1) (t 2))
  let c := max (t 0) (max (t 1) (t 2))
  shape a (t 0 + t 1 + t 2 - a - c) c

def secondTypes : List Shape :=
  [shape 1 1 6, shape 1 2 5, shape 1 3 4, shape 2 2 4, shape 2 3 3]

def buildMasses (a : Law Shape) (splits : List (Shape × Law Shape)) : Build (Law Shape) :=
  (shapes 8).mapM fun t => do
    let terms ← positiveInitial.mapM fun g => do
      mul (getLaw a g) (getLaw (getSplit splits g) t)
    let mass ← sumRefs terms
    pure (t, ← mul mass (← lit 2))

def buildLittleMasses (m : Law Shape) (splits : List (Shape × Law Shape)) :
    Build (Law (Shape × Shape)) := do
  let mut result := []
  for t in positiveSecond do
    for (u,mass) in getSplit splits t do
      let v ← mul (getLaw m t) (← lit 2)
      result := result ++ [((t,u), ← mul v mass)]
  pure result

def addRow [BEq α] (rows : List (α × List Ref)) (key : α) (mass : Ref)
    (caps : List Ref) : Build (List (α × List Ref)) := do
  rows.mapM fun (k,row) => do
    if k == key then
      pure (k, ← (List.range 3).mapM fun i => do
        add (row[i]?.getD 0) (← mul mass (caps[i]?.getD 0)))
    else pure (k,row)

def rowTotals (rows : List (α × List Ref)) : Build (List Ref) :=
  (List.range 3).mapM fun i => sumRefs (rows.map fun row => row.2[i]?.getD 0)

def binaryEntropy (d : Ref) : Build Ref := do
  add (← entropy [← sub 1 d,d]) (← mul d (← log (← lit 2)))

def coefficientStep (xs : List Nat) : List Nat :=
  (List.range (xs.length + 2)).map fun i =>
    (xs[i]?.getD 0) + (if i > 0 then 5 * xs[i-1]?.getD 0 else 0) +
      (if i > 1 then xs[i-2]?.getD 0 else 0)

def coefficients : List Nat := (List.range 8).foldl (fun xs _ => coefficientStep xs) [1]

structure Roots where
  weights : Law ℤ
  initial : Law Shape
  stageA : List (Shape × Law Shape)
  stageB : List (Shape × Law Shape)
  binary : Law (Shape × Shape)
  zeroPairs : List (Shape × Law PairSlot)
  halfLaws : List ((Shape × Fin 3) × Law PairSlot)
  masses : Law Shape
  littleMasses : Law (Shape × Shape)
  rowsA : List (Nat × List Ref)
  rowsB : List (Shape × List Ref)
  LA : List Ref
  LB : List Ref
  LAB : List Ref
  LC : List Ref
  lambda : List Ref
  LCdirect : List Ref
  H0 : Ref
  B : Ref
  T : Ref
  C : Ref
  S0 : Ref
  S1 : Ref
  S2 : Ref
  S : Ref
  rhs : Ref
  exponent : Ref
  denominatorSlack : Ref
  balanceSlacks : List Ref
  thresholdGap : Ref
  deriving DecidableEq

def buildAll : Build Roots := do
  let _ ← lit 0
  let _ ← lit 1
  let weights ← buildWeights
  let a ← buildInitial weights
  let pa ← buildSplit weights positiveInitial tableP
  let pb ← buildSplit weights positiveSecond tablep
  let binary ← buildBinary
  let zpairs ← buildZeroPairs weights
  let half ← buildHalfLaws pb binary zpairs
  let m ← buildMasses a pa
  let mu ← buildLittleMasses m pb
  let mut rowsA := (List.range 5).map fun i => (i+1,[0,0,0])
  let mut rowsB := secondTypes.map fun t => (t,[0,0,0])
  for t in positiveSecond do
    let caps ← capacity t (getSplit pb t) (priority t) (littleLaw binary t)
    rowsB ← addRow rowsB (sortShape t) (getLaw m t) caps
  for g in positiveInitial do
    let caps ← capacity g (getSplit pa g) (0,1,2) (fun t w => pure (getHalf half t w))
    rowsA ← addRow rowsA (g 0) (getLaw a g) caps
  let la ← rowTotals rowsA
  let lb ← rowTotals rowsB
  let lab ← (List.range 3).mapM fun i => add (la[i]?.getD 0) (lb[i]?.getD 0)
  let interior := mu.filter fun e => positive e.1.2
  let total ← sumRefs (interior.map Prod.snd)
  let bterms ← interior.mapM fun ((t,u),mass) => do
    let rate ← add (← mul (← log (← lit 2)) (← lit 2))
      (← binaryEntropy (getLaw binary (t,u)))
    divide (← mul mass rate) (← lit 3)
  let b ← sumRefs bterms
  let c ← add b (← divide (← sumRefs lab) (← lit 3))
  let lc ← lab.mapM (sub c)
  let lambda ← (List.range 3).mapM fun i => do
    let numerator ← sub (← mul total (← log (← lit 2))) (lc[i]?.getD 0)
    let denominator ← sub (← mul total (← log (← lit 2))) b
    divide numerator (← mul denominator (← lit 3))
  let direct ← (List.range 3).mapM fun i => do
    let terms ← interior.mapM fun ((t,u),mass) => do
      let left ← mul (← sub 1 (lambda[i]?.getD 0)) (← log (← lit 2))
      let right ← mul (lambda[i]?.getD 0) (← binaryEntropy (getLaw binary (t,u)))
      mul mass (← add left right)
    sumRefs terms
  let mut marginal := []
  for (g,mass) in a do
    for w in ([0,1,2] : List (Fin 3)) do
      marginal ← addMass marginal (g w) (← divide mass (← lit 3))
  let h0 ← entropy (marginal.map Prod.snd)
  let s0terms ← (a.filter fun e => !positive e.1).mapM fun (g,mass) => do
    mul mass (← log (← lit (coefficients[shapeMax g]?.getD 0)))
  let s0 ← sumRefs s0terms
  let s1terms ← zeroSecond.mapM fun t => do
    let law := getPairs zpairs t
    let ent ← entropy (law.map Prod.snd)
    let terms ← law.mapM fun ((i,j),mass) => do
      mul mass (← log (← lit (multiplicity i * multiplicity j)))
    mul (getLaw m t) (← add ent (← sumRefs terms))
  let s1 ← sumRefs s1terms
  let mut s2 := 0
  for ((t,u),mass) in mu do
    let d := getLaw binary (t,u)
    let rate ← if shapeMax u = 4 then pure 0
      else if shapeMax u = 3 then log (← lit 10)
      else if !positive u then do
        let first ← binaryEntropy d
        let second ← mul (← mul (← sub 1 d) (← lit 2)) (← log (← lit 5))
        add first second
      else mul (← sub (← lit 2) d) (← log (← lit 5))
    s2 ← add s2 (← mul mass rate)
  let volume ← add (← add s0 s1) s2
  let rhs ← mul (← log (← lit 7)) (← lit 8)
  let exponent ← divide (← mul (← sub (← sub rhs h0) c) (← lit 3)) volume
  let denominatorSlack ← sub (← mul total (← log (← lit 2))) b
  let balanceSlacks ← lc.mapM fun v => do sub (← mul total (← log (← lit 2))) v
  let thresholdGap ← sub (← lit ((2371054887 : ℚ) / 10^9)) exponent
  pure {
    weights := weights
    initial := a
    stageA := pa
    stageB := pb
    binary := binary
    zeroPairs := zpairs
    halfLaws := half
    masses := m
    littleMasses := mu
    rowsA := rowsA
    rowsB := rowsB
    LA := la
    LB := lb
    LAB := lab
    LC := lc
    lambda := lambda
    LCdirect := direct
    H0 := h0
    B := b
    T := total
    C := c
    S0 := s0
    S1 := s1
    S2 := s2
    S := volume
    rhs := rhs
    exponent := exponent
    denominatorSlack := denominatorSlack
    balanceSlacks := balanceSlacks
    thresholdGap := thresholdGap }

def built := buildAll.run {}

def program : Program := built.2.program

def roots : Roots := built.1

noncomputable def exponent : ℝ := program.eval[roots.exponent]?.getD 0

noncomputable def scalar (root : Ref) : ℝ := program.eval[root]?.getD 0

noncomputable def Y : ℝ := scalar roots.H0 + scalar roots.C

noncomputable def S : ℝ := scalar roots.S

noncomputable def R : ℝ := 8 * Real.log 7

noncomputable def ratio : ℝ := 3 * (R - Y) / S

end MatrixMultiplication.AllFieldParameters.Contractions

end OAI

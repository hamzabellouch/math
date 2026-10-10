import Mathlib

namespace OAI

namespace VariableWL

abbrev Word := List Bool

inductive Motion where
  | left | stay | right
  deriving DecidableEq

def Motion.displacement : Motion → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure Machine where
  states : ℕ
  workSymbols : ℕ
  extraTapes : ℕ
  transition : Fin (states + 1) →
    (Fin (extraTapes + 1) → Fin (workSymbols + 3)) →
    Option (Fin (states + 1) ×
      (Fin (extraTapes + 1) → Fin (workSymbols + 3) × Motion))

structure Configuration (M : Machine) where
  control : Fin (M.states + 1)
  heads : Fin (M.extraTapes + 1) → ℤ
  cells : Fin (M.extraTapes + 1) → ℤ → Fin (M.workSymbols + 3)

def wordCells (a : ℕ) (w : Word) (i : ℤ) : Fin (a + 3) :=
  if 0 ≤ i then
    match w[i.toNat]? with
    | none => 0
    | some false => 1
    | some true => 2
  else 0

def initial (M : Machine) (w : Word) : Configuration M where
  control := 0
  heads := fun _ => 0
  cells := fun j => if j = 0 then wordCells M.workSymbols w else fun _ => 0

def scanned {M : Machine} (c : Configuration M) :
    Fin (M.extraTapes + 1) → Fin (M.workSymbols + 3) :=
  fun j => c.cells j (c.heads j)

def step (M : Machine) (c : Configuration M) : Option (Configuration M) :=
  (M.transition c.control (scanned c)).map fun data =>
    { control := data.1
      heads := fun j => c.heads j + (data.2 j).2.displacement
      cells := fun j i => if i = c.heads j then (data.2 j).1 else c.cells j i }

def run (M : Machine) (w : Word) : ℕ → Configuration M
  | 0 => initial M w
  | n + 1 => (step M (run M w n)).getD (run M w n)

def OutputsWithin (M : Machine) (w out : Word) (bound : ℕ) : Prop :=
  ∃ t ≤ bound, step M (run M w t) = none ∧
    (run M w t).cells 0 = wordCells M.workSymbols out

abbrev Language := Set Word

def InEXPTIME (L : Language) : Prop :=
  ∃ M : Machine, ∃ c d : ℕ, ∀ w : Word,
    ∃ b : Bool, (b = true ↔ w ∈ L) ∧
      OutputsWithin M w [b] (2 ^ (c * (w.length + 1) ^ d))

def PolytimeReduces (L R : Language) : Prop :=
  ∃ M : Machine, ∃ c d : ℕ, ∀ w : Word,
    ∃ out : Word, OutputsWithin M w out (c * (w.length + 1) ^ d) ∧
      (w ∈ L ↔ out ∈ R)

def EXPTIMEComplete (L : Language) : Prop :=
  InEXPTIME L ∧ ∀ R : Language, InEXPTIME R → PolytimeReduces R L

structure Graph where
  order : ℕ
  graph : SimpleGraph (Fin order)

abbrev Tuple (G : Graph) (k : ℕ) := Fin k → Fin G.order

def Color (k : ℕ) : ℕ → Type
  | 0 => Fin k → Fin k → Bool × Bool
  | s + 1 => Color k s × Multiset (Fin k → Color k s)

noncomputable def color (G : Graph) (k : ℕ) : (s : ℕ) → Tuple G k → Color k s
  | 0, v => by
      classical
      exact fun i j => (decide (v i = v j), decide (G.graph.Adj (v i) (v j)))
  | s + 1, v => (color G k s v,
      Finset.univ.val.map (fun z => fun i => color G k s (Function.update v i z)))

noncomputable def histogram (G : Graph) (k s : ℕ) : Multiset (Color k s) :=
  Finset.univ.val.map (color G k s)

def Equivalent (G H : Graph) (k : ℕ) : Prop :=
  ∀ s : ℕ, histogram G k s = histogram H k s

def integerCode (n : ℕ) : Word :=
  List.replicate (Nat.bits n).length true ++ [false] ++ Nat.bits n

noncomputable def graphCode (G : Graph) : Word := by
  classical
  exact integerCode G.order ++
    (List.ofFn fun i : Fin G.order =>
      List.ofFn fun j : Fin G.order => decide (G.graph.Adj i j)).flatten

noncomputable def pairCode (G H : Graph) (k : ℕ) : Word :=
  graphCode G ++ graphCode H ++ integerCode k

def WL : Language :=
  { w | ∃ G H : Graph, ∃ k : ℕ, w = pairCode G H k ∧ 2 ≤ k ∧ Equivalent G H k }

noncomputable def Subcubic (G : Graph) : Prop := by
  classical
  exact ∀ v : Fin G.order, G.graph.degree v ≤ 3

def SubWL : Language :=
  { w | ∃ G H : Graph, ∃ k : ℕ, w = pairCode G H k ∧ 2 ≤ k ∧
    0 < G.order ∧ G.order = H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
    Subcubic G ∧ Subcubic H ∧ Equivalent G H k }

theorem main : EXPTIMEComplete WL ∧ EXPTIMEComplete SubWL := by
  sorry

end VariableWL

end OAI

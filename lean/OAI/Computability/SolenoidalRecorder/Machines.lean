import Mathlib

namespace OAI

/-! Normalized finite machines and bounded work-head displacement. -/

namespace Solenoidal
 
inductive Move
  | left | stay | right
  deriving DecidableEq, Repr

protected abbrev Move.enumList : List Move := [.left, .stay, .right]

protected theorem Move.enumList_getElem?_ctorIdx_eq (x : Move) :
    Move.enumList[Move.ctorIdx x]? = some x := by
  cases x <;> rfl

protected theorem Move.enumList_nodup : Move.enumList.Nodup := by
  decide

instance : Fintype Move where
  elems := ⟨Move.enumList, Move.enumList_nodup⟩
  complete x := by
    cases x <;> decide

@[simp] def Move.displacement : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

theorem Move.abs_displacement_le (d : Move) : |d.displacement| ≤ 1 := by
  cases d <;> norm_num

 

structure Machine where
  states : ℕ
  symbols : ℕ
  initial : Fin (states + 1)
  blank : Fin (symbols + 1)
  halt : Fin (states + 1) → Bool
  table : Fin (states + 1) → Fin (symbols + 1) →
    Fin (states + 1) × Fin (symbols + 1) × Move

namespace Machine

abbrev State (M : Machine) := Fin (M.states + 1)
abbrev Symbol (M : Machine) := Fin (M.symbols + 1)

@[ext] structure Config (M : Machine) where
  state : M.State
  head : ℤ
  tape : ℤ → M.Symbol

 

def step (M : Machine) (c : M.Config) : M.Config :=
  if M.halt c.state then c else
    let r := M.table c.state (c.tape c.head)
    ⟨r.1, c.head + r.2.2.displacement, Function.update c.tape c.head r.2.1⟩

 
def inputTape (M : Machine) (w : List M.Symbol) (k : ℤ) : M.Symbol :=
  if 0 ≤ k then w[k.toNat]?.getD M.blank else M.blank

def initialConfig (M : Machine) (w : List M.Symbol) : M.Config :=
  ⟨M.initial, 0, M.inputTape w⟩

def run (M : Machine) (w : List M.Symbol) (n : ℕ) : M.Config :=
  (M.step^[n]) (M.initialConfig w)

def Halts (M : Machine) (w : List M.Symbol) : Prop :=
  ∃ n : ℕ, M.halt (M.run w n).state = true

theorem halts_of_initial (M : Machine) (w : List M.Symbol)
    (h : M.halt M.initial = true) : M.Halts w := by
  exact ⟨0, h⟩

 
theorem step_head_bound (M : Machine) (c : M.Config) :
    |(M.step c).head| ≤ |c.head| + 1 := by
  simp only [step]
  split
  · omega
  · dsimp
    exact (abs_add_le _ _).trans
      (add_le_add le_rfl ((M.table c.state (c.tape c.head)).2.2.abs_displacement_le))

theorem run_succ (M : Machine) (w : List M.Symbol) (n : ℕ) :
    M.run w (n + 1) = M.step (M.run w n) := by
  exact Function.iterate_succ_apply' _ _ _

 
theorem run_head_bound (M : Machine) (w : List M.Symbol) (n : ℕ) :
    |(M.run w n).head| ≤ (n : ℤ) := by
  induction n with
  | zero => simp [run, initialConfig]
  | succ n ih =>
    rw [run_succ]
    exact (step_head_bound M (M.run w n)).trans (by omega)

 
abbrev Instruction (M : Machine) :=
  {r : M.State × M.Symbol // M.halt r.1 = false}

namespace Instruction
variable {M : Machine}
def oldState (r : M.Instruction) : M.State := r.val.1
def read (r : M.Instruction) : M.Symbol := r.val.2
def nextState (r : M.Instruction) : M.State := (M.table r.oldState r.read).1
def write (r : M.Instruction) : M.Symbol := (M.table r.oldState r.read).2.1
def move (r : M.Instruction) : Move := (M.table r.oldState r.read).2.2
end Instruction

end Machine
end Solenoidal

end OAI

import OAI.Combinatorics.ParityLifts.Main

namespace OAI

namespace ParityWL

/-! Finite-alphabet deterministic multitape model.
A transition reads and writes only the currently scanned
cell on each tape and moves each head by at most one cell. -/
namespace Complexity

inductive Move | left | stay | right
  deriving DecidableEq

instance : Fintype Move :=
  ⟨{Move.left, Move.stay, Move.right}, by intro x; cases x <;> simp⟩

def Move.offset : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- Blank is 0, input bits are 1 and 2. Every work alphabet, state space and
collection of tapes is finite. Tapes are two-way infinite. -/
structure Machine where
  tapes : ℕ
  extraSymbols : ℕ
  extraStates : ℕ
  initial : Fin (extraStates + 1)
  output : Fin (extraStates + 1) → Option Bool
  transition : Fin (extraStates + 1) →
    (Fin (tapes + 1) → Fin (extraSymbols + 3)) →
    Fin (extraStates + 1) × (Fin (tapes + 1) → Fin (extraSymbols + 3) × Move)

structure Configuration (M : Machine) where
  state : Fin (M.extraStates + 1)
  head : Fin (M.tapes + 1) → ℤ
  tape : Fin (M.tapes + 1) → ℤ → Fin (M.extraSymbols + 3)

def inputSymbol (M : Machine) (b : Bool) : Fin (M.extraSymbols + 3) :=
  if b then ⟨2, by omega⟩ else ⟨1, by omega⟩

def initialConfiguration (M : Machine) (input : List Bool) : Configuration M where
  state := M.initial
  head := fun _ => 0
  tape := fun i z => if i.val = 0 ∧ 0 ≤ z then
    match input[z.toNat]? with
    | some b => inputSymbol M b
    | none => 0
    else 0

def step (M : Machine) (x : Configuration M) : Configuration M :=
  match M.output x.state with
  | some _ => x
  | none =>
      let a := M.transition x.state (fun i => x.tape i (x.head i))
      { state := a.1
        head := fun i => x.head i + (a.2 i).2.offset
        tape := fun i z => if z = x.head i then (a.2 i).1 else x.tape i z }

def run (M : Machine) (input : List Bool) (s : ℕ) : Configuration M :=
  (step M)^[s] (initialConfiguration M input)

def Emits (M : Machine) (input : List Bool) (s : ℕ) (b : Bool) : Prop :=
  M.output (run M input s).state = some b


end Complexity
end ParityWL

namespace ParityWL.Complexity

/-- A finite-control presentation of the very same local multitape model.
`packed` below changes ONLY the names of states, with zero simulation cost. -/
structure LocalMachine (Q : Type) (t a : ℕ) where
  initial : Q
  output : Q → Option Bool
  transition : Q → (Fin (t + 1) → Fin (a + 3)) →
    Q × (Fin (t + 1) → Fin (a + 3) × Move)

structure LocalConfiguration (Q : Type) (t a : ℕ) where
  state : Q
  head : Fin (t + 1) → ℤ
  tape : Fin (t + 1) → ℤ → Fin (a + 3)

def localInputSymbol (a : ℕ) (b : Bool) : Fin (a + 3) :=
  if b then ⟨2, by omega⟩ else ⟨1, by omega⟩

def LocalMachine.initialConfiguration {Q : Type} {t a : ℕ}
    (P : LocalMachine Q t a) (input : List Bool) : LocalConfiguration Q t a where
  state := P.initial
  head := fun _ => 0
  tape := fun i z => if i.val = 0 ∧ 0 ≤ z then
    match input[z.toNat]? with
    | some b => localInputSymbol a b
    | none => 0
    else 0

def LocalMachine.step {Q : Type} {t a : ℕ} (P : LocalMachine Q t a)
    (x : LocalConfiguration Q t a) : LocalConfiguration Q t a :=
  match P.output x.state with
  | some _ => x
  | none =>
      let b := P.transition x.state (fun i => x.tape i (x.head i))
      { state := b.1
        head := fun i => x.head i + (b.2 i).2.offset
        tape := fun i z => if z = x.head i then (b.2 i).1 else x.tape i z }

def LocalMachine.run {Q : Type} {t a : ℕ} (P : LocalMachine Q t a)
    (input : List Bool) (s : ℕ) : LocalConfiguration Q t a :=
  P.step^[s] (P.initialConfiguration input)

noncomputable def LocalMachine.stateEquiv {Q : Type} [Fintype Q] {t a : ℕ}
    (P : LocalMachine Q t a) : Q ≃ Fin (Fintype.card Q - 1 + 1) := by
  have hcard : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨P.initial⟩
  exact Fintype.equivFinOfCardEq (by omega)

noncomputable def LocalMachine.packed {Q : Type} [Fintype Q] {t a : ℕ}
    (P : LocalMachine Q t a) : Machine where
  tapes := t
  extraSymbols := a
  extraStates := Fintype.card Q - 1
  initial := P.stateEquiv P.initial
  output := fun q => P.output (P.stateEquiv.symm q)
  transition := fun q x => let b := P.transition (P.stateEquiv.symm q) x
    (P.stateEquiv b.1, b.2)

noncomputable def LocalMachine.packConfiguration {Q : Type} [Fintype Q] {t a : ℕ}
    (P : LocalMachine Q t a) (x : LocalConfiguration Q t a) : Configuration P.packed where
  state := P.stateEquiv x.state
  head := x.head
  tape := x.tape

lemma LocalMachine.pack_initial {Q : Type} [Fintype Q] {t a : ℕ}
    (P : LocalMachine Q t a) (input : List Bool) :
    P.packConfiguration (P.initialConfiguration input) = Complexity.initialConfiguration P.packed input := by
  rfl

lemma LocalMachine.pack_step {Q : Type} [Fintype Q] {t a : ℕ}
    (P : LocalMachine Q t a) (x : LocalConfiguration Q t a) :
    P.packConfiguration (P.step x) = Complexity.step P.packed (P.packConfiguration x) := by
  simp only [LocalMachine.step, Complexity.step, LocalMachine.packConfiguration, LocalMachine.packed,
    Equiv.symm_apply_apply]
  cases h : P.output x.state <;> rfl

lemma LocalMachine.pack_run {Q : Type} [Fintype Q] {t a : ℕ}
    (P : LocalMachine Q t a) (input : List Bool) (s : ℕ) :
    P.packConfiguration (P.run input s) = Complexity.run P.packed input s := by
  induction s with
  | zero => exact P.pack_initial input
  | succ s ih =>
    simpa only [LocalMachine.run, Complexity.run, Function.iterate_succ_apply', P.pack_step] using
      congrArg (Complexity.step P.packed) ih

lemma LocalMachine.packed_emits {Q : Type} [Fintype Q] {t a : ℕ}
    (P : LocalMachine Q t a) (input : List Bool) (s : ℕ) (b : Bool) :
    Emits P.packed input s b ↔ P.output (P.run input s).state = some b := by
  unfold Emits
  rw [← P.pack_run]
  simp only [LocalMachine.packed, LocalMachine.packConfiguration, Equiv.symm_apply_apply]

end ParityWL.Complexity

end OAI

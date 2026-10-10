import Mathlib.Data.Fintype.Sigma
import OAI.Computability.BinPacking.Arithmetic.PackingRegisterUpdate
import OAI.Computability.BinPacking.Packing.PackingAssignments
import OAI.Computability.BinPacking.Packing.PairExpressionCompiler

namespace OAI

noncomputable section

namespace BinPackingGap.PackingMachineLayout

open NatExpressionCompiler PairExpressionCompiler BinaryRegisterProgram
open PackingRegisterFrame

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input]

abbrev Reg (num : Descriptor → Expr Input) (den : Expr Input) (Other : Type) :=
  (Input ⊕ Other) ⊕ (Σ d : Descriptor, Node (num d) ⊕ Node den)

abbrev Tape (num : Descriptor → Expr Input) (den : Expr Input)
    (Other Extra : Type) := (Reg num den Other ⊕ Fin 6) ⊕ Extra

instance regDecidableEq (num : Descriptor → Expr Input) (den : Expr Input)
    [DecidableEq Other] : DecidableEq (Reg num den Other) :=
  inferInstanceAs (DecidableEq ((Input ⊕ Other) ⊕ (Σ d : Descriptor, Node (num d) ⊕ Node den)))

instance tapeDecidableEq (num : Descriptor → Expr Input) (den : Expr Input)
    [DecidableEq Other] [DecidableEq Extra] : DecidableEq (Tape num den Other Extra) :=
  inferInstanceAs (DecidableEq ((Reg num den Other ⊕ Fin 6) ⊕ Extra))

def registers (num : Descriptor → Expr Input) (den : Expr Input) :
    (Reg num den Other ⊕ Fin 6) ↪ Tape num den Other Extra := Function.Embedding.inl

def inputs (num : Descriptor → Expr Input) (den : Expr Input) : Input ↪ Reg num den Other where
  toFun a := .inl (.inl a)
  inj' := by intro a b h; exact Sum.inl.inj (Sum.inl.inj h)

def others (num : Descriptor → Expr Input) (den : Expr Input) : Other ↪ Reg num den Other where
  toFun a := .inl (.inr a)
  inj' := by intro a b h; exact Sum.inr.inj (Sum.inl.inj h)

def itemRegisters (num : Descriptor → Expr Input) (den : Expr Input) (d : Descriptor) :
    PairExpressionCompiler.Reg (num d) den ↪ Reg num den Other where
  toFun
    | .inl a => inputs num den a
    | .inr node => .inr ⟨d, node⟩
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl ((inputs num den).injective h)
        | inr b => cases h
    | inr a =>
        cases b with
        | inl b => cases h
        | inr b =>
            have hs : (⟨d, a⟩ : Σ d : Descriptor, Node (num d) ⊕ Node den) = ⟨d, b⟩ :=
              Sum.inr.inj h
            exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj_iff.mp hs).2)

def itemSlots (num : Descriptor → Expr Input) (den : Expr Input) (d : Descriptor) :
    (PairExpressionCompiler.Reg (num d) den ⊕ Fin 6) ↪ Tape num den Other Extra :=
  localSlots (registers num den) (itemRegisters num den d)

def values (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) : Reg num den Other → Nat
  | .inl (.inl a) => input a
  | .inl (.inr b) => other b
  | .inr _ => 0

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem values_inputs (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (a : Input) :
    values num den input other (inputs num den a) = input a := rfl

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem values_others (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (a : Other) :
    values num den input other (others num den a) = other a := rfl

omit [DecidableEq Descriptor] [DecidableEq Input] in
theorem values_itemRegisters (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (d : Descriptor) :
    values num den input other ∘ itemRegisters num den d =
      initial (num d) den input := by
  funext r
  cases r <;> rfl

variable [DecidableEq Other] [DecidableEq Extra]

def tapes (num : Descriptor → Expr Input) (den : Expr Input)
    (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) : Tape num den Other Extra → List Bool :=
  registerTapes (registers num den) base (values num den input other)

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
theorem item_shape (num : Descriptor → Expr Input) (den : Expr Input)
    (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (d : Descriptor) :
    registerTapes (itemSlots num den d) (tapes num den base input other)
      (initial (num d) den input) = tapes num den base input other := by
  classical
  rw [← values_itemRegisters num den input other d]
  exact restrict (registers num den) (itemRegisters num den d) base
    (values num den input other)

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
theorem itemSlots_outside (num : Descriptor → Expr Input) (den : Expr Input)
    (d : Descriptor) (output : Extra) (i : PairExpressionCompiler.Reg (num d) den ⊕ Fin 6) :
    itemSlots (Other := Other) num den d i ≠ Sum.inr output := by
  simp only [itemSlots, localSlots, Function.Embedding.trans_apply, registers,
    Function.Embedding.inl_apply, ne_eq, Sum.inl_ne_inr, not_false_eq_true]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
@[simp] theorem tapes_extra (num : Descriptor → Expr Input) (den : Expr Input)
    (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (k : Extra) :
    tapes num den base input other (.inr k) = base (.inr k) := by
  apply registerTapes_other
  rintro ⟨i, hi⟩
  cases hi

theorem values_update_input (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (a : Input) (n : Nat) :
    values num den (Function.update input a n) other =
      Function.update (values num den input other) (inputs num den a) n := by
  change values num den (Function.update input a n) other =
    Function.update (values num den input other) (.inl (.inl a)) n
  funext r
  cases r with
  | inl r =>
      cases r with
      | inl b => simp [values, Function.update_apply]
      | inr b => simp [values]
  | inr node => simp [values]

theorem values_update_other (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (a : Other) (n : Nat) :
    values num den input (Function.update other a n) =
      Function.update (values num den input other) (others num den a) n := by
  change values num den input (Function.update other a n) =
    Function.update (values num den input other) (.inl (.inr a)) n
  funext r
  cases r with
  | inl r =>
      cases r with
      | inl b => simp [values]
      | inr b => simp [values, Function.update_apply]
  | inr node => simp [values]

end BinPackingGap.PackingMachineLayout

namespace BinPackingGap.PackingLayoutCommands

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open PackingMachineLayout

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] in
theorem values_width (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∀ r, (values num den input other r).size ≤ width := by
  intro r
  rcases r with (a | b) | node
  · exact hi a
  · exact ho b
  · simp [values]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] in
private theorem input_ne_other (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (source : Other) :
    inputs num den destination ≠ others num den source := by
  change (Sum.inl (Sum.inl destination) : Reg num den Other) ≠ Sum.inl (Sum.inr source)
  simp

def inputFromOther (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (source : Other) :
    Code (K := Tape num den Other Extra) (S := State) :=
  PackingAssignments.copy (registers num den) (inputs num den destination)
    (others num den source) (input_ne_other num den destination source)

def inputFromOtherTime (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (source : Other) : Polynomial Nat :=
  runtimePolynomial (PackingAssignments.copyCommands (inputs num den destination)
    (others num den source) (input_ne_other num den destination source)) + 2

theorem inputFromOther_exec (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (source : Other) (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (state : State) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ (inputFromOtherTime num den destination source).eval width,
      Exec (inputFromOther num den destination source)
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den base (Function.update input destination (other source)) other⟩ := by
  have run := PackingAssignments.copy_exec (registers (Extra := Extra) num den)
    (inputs num den destination) (others num den source) (input_ne_other num den destination source)
    base (values num den input other) state width (values_width num den input other width hi ho)
  rw [values_others, ← values_update_input] at run
  simpa only [inputFromOther, inputFromOtherTime, Polynomial.eval_add,
    Polynomial.eval_ofNat, tapes] using run

def otherFromInput (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Other) (source : Input) :
    Code (K := Tape num den Other Extra) (S := State) :=
  PackingAssignments.copy (registers num den) (others num den destination)
    (inputs num den source) (input_ne_other num den source destination).symm

def otherFromInputTime (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Other) (source : Input) : Polynomial Nat :=
  runtimePolynomial (PackingAssignments.copyCommands (others num den destination)
    (inputs num den source) (input_ne_other num den source destination).symm) + 2

theorem otherFromInput_exec (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Other) (source : Input) (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (state : State) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ (otherFromInputTime num den destination source).eval width,
      Exec (otherFromInput num den destination source)
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den base input (Function.update other destination (input source))⟩ := by
  have run := PackingAssignments.copy_exec (registers (Extra := Extra) num den)
    (others num den destination) (inputs num den source) (input_ne_other num den source destination).symm
    base (values num den input other) state width (values_width num den input other width hi ho)
  rw [values_inputs, ← values_update_other] at run
  simpa only [otherFromInput, otherFromInputTime, Polynomial.eval_add,
    Polynomial.eval_ofNat, tapes] using run

def setInput (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (constant : Nat) :
    Code (K := Tape num den Other Extra) (S := State) :=
  PackingAssignments.setConstant (registers num den) (inputs num den destination) constant

def setInputTime (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (constant : Nat) : Polynomial Nat :=
  runtimePolynomial (PackingAssignments.constantCommands
    (inputs (Other := Other) num den destination) constant) + 2

theorem setInput_exec (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (constant : Nat) (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (state : State) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ (setInputTime (Other := Other) num den destination constant).eval width,
      Exec (setInput num den destination constant)
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den base (Function.update input destination constant) other⟩ := by
  have run := PackingAssignments.constant_exec (registers (Extra := Extra) num den)
    (inputs num den destination) constant base (values num den input other) state width
    (values_width num den input other width hi ho)
  rw [← values_update_input] at run
  simpa only [setInput, setInputTime, Polynomial.eval_add, Polynomial.eval_ofNat, tapes] using run

def setOther (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Other) (constant : Nat) :
    Code (K := Tape num den Other Extra) (S := State) :=
  PackingAssignments.setConstant (registers num den) (others num den destination) constant

def setOtherTime (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Other) (constant : Nat) : Polynomial Nat :=
  runtimePolynomial (PackingAssignments.constantCommands
    (others num den destination) constant) + 2

theorem setOther_exec (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Other) (constant : Nat) (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (state : State) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ (setOtherTime num den destination constant).eval width,
      Exec (setOther num den destination constant)
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den base input (Function.update other destination constant)⟩ := by
  have run := PackingAssignments.constant_exec (registers (Extra := Extra) num den)
    (others num den destination) constant base (values num den input other) state width
    (values_width num den input other width hi ho)
  rw [← values_update_other] at run
  simpa only [setOther, setOtherTime, Polynomial.eval_add, Polynomial.eval_ofNat, tapes] using run

end BinPackingGap.PackingLayoutCommands

namespace BinPackingGap.PackingVertexUpdate

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input]

def updateRegisters (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    Fin 3 ↪ PackingMachineLayout.Reg num den Other where
  toFun := ![Sum.inl (Sum.inr three), Sum.inl (Sum.inl power),
    Sum.inl (Sum.inr temporary)]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Ne.symm distinct]

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem updateRegisters_zero (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    updateRegisters num den power three temporary distinct 0 =
      PackingMachineLayout.others num den three := rfl

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem updateRegisters_one (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    updateRegisters num den power three temporary distinct 1 =
      PackingMachineLayout.inputs num den power := rfl

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem updateRegisters_two (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    updateRegisters num den power three temporary distinct 2 =
      PackingMachineLayout.others num den temporary := rfl

def updateSlots (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    (Fin 3 ⊕ Fin 6) ↪ PackingMachineLayout.Tape num den Other Extra :=
  PackingRegisterFrame.localSlots (PackingMachineLayout.registers num den)
    (updateRegisters num den power three temporary distinct)

omit [DecidableEq Descriptor] [DecidableEq Input] in
theorem values_updateRegisters (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary)
    (input : Input → Nat) (other : Other → Nat)
    (hthree : other three = 3) (htemporary : other temporary = 0) :
    PackingMachineLayout.values num den input other ∘
        updateRegisters num den power three temporary distinct =
      PackingRegisterUpdate.values 3 (input power) := by
  funext r
  fin_cases r <;>
    simp [PackingRegisterUpdate.values, hthree, htemporary]

variable [DecidableEq Other] [DecidableEq Extra]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
theorem shape (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat)
    (hthree : other three = 3) (htemporary : other temporary = 0) :
    registerTapes (updateSlots num den power three temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values 3 (input power)) =
      PackingMachineLayout.tapes num den base input other := by
  rw [← values_updateRegisters num den power three temporary distinct input other
    hthree htemporary]
  exact PackingRegisterFrame.restrict (PackingMachineLayout.registers num den)
    (updateRegisters num den power three temporary distinct) base
    (PackingMachineLayout.values num den input other)

omit [DecidableEq Extra] in
theorem updated_shape (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat)
    (hthree : other three = 3) (htemporary : other temporary = 0) :
    registerTapes (updateSlots num den power three temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values 3 (3 * input power)) =
      PackingMachineLayout.tapes num den base
        (Function.update input power (3 * input power)) other := by
  apply PackingRegisterFrame.replace (PackingMachineLayout.registers num den)
    (updateRegisters num den power three temporary distinct) base
    (PackingMachineLayout.values num den input other)
    (PackingMachineLayout.values num den (Function.update input power (3 * input power)) other)
    (PackingRegisterUpdate.values 3 (3 * input power))
  · intro r
    fin_cases r <;> simp [PackingRegisterUpdate.values, hthree, htemporary]
  · intro r hr
    have hrne : r ≠ PackingMachineLayout.inputs num den power := by
      intro heq
      apply hr
      refine ⟨1, ?_⟩
      simpa only [updateRegisters_one] using heq.symm
    simp only [PackingMachineLayout.values_update_input, Function.update_of_ne hrne]

theorem exec (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat)
    (hthree : other three = 3) (htemporary : other temporary = 0)
    (state : PackingMachineBlocks.State) :
    ∃ steps ≤ 64 * ((3 : Nat).size + (input power).size + 1) ^ 2,
      Exec (PackingRegisterUpdate.code
          (updateSlots num den power three temporary distinct) .multiply)
        ⟨state, PackingMachineLayout.tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          PackingMachineLayout.tapes num den base
            (Function.update input power (3 * input power)) other⟩ := by
  obtain ⟨steps, hsteps, hrun⟩ := PackingRegisterUpdate.exec
    (updateSlots num den power three temporary distinct) .multiply
    (PackingMachineLayout.tapes num den base input other) 3 (input power) state
  refine ⟨steps, hsteps, ?_⟩
  change Exec (PackingRegisterUpdate.code
      (updateSlots num den power three temporary distinct) .multiply)
    ⟨state, registerTapes (updateSlots num den power three temporary distinct)
      (PackingMachineLayout.tapes num den base input other)
      (PackingRegisterUpdate.values 3 (input power))⟩ steps
    ⟨.arithmetic (BinaryAddMachine.clean ()),
      registerTapes (updateSlots num den power three temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values 3 (3 * input power))⟩ at hrun
  rw [shape num den power three temporary distinct base input other hthree htemporary,
    updated_shape num den power three temporary distinct base input other hthree htemporary] at hrun
  exact hrun

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
theorem general_shape (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (baseRegister temporary : Other) (distinct : baseRegister ≠ temporary)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (htemporary : other temporary = 0) :
    registerTapes (updateSlots num den power baseRegister temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values (other baseRegister) (input power)) =
      PackingMachineLayout.tapes num den base input other := by
  have hvalues : PackingMachineLayout.values num den input other ∘
      updateRegisters num den power baseRegister temporary distinct =
        PackingRegisterUpdate.values (other baseRegister) (input power) := by
    funext r
    fin_cases r <;> simp [PackingRegisterUpdate.values, htemporary]
  rw [← hvalues]
  exact PackingRegisterFrame.restrict (PackingMachineLayout.registers num den)
    (updateRegisters num den power baseRegister temporary distinct) base
    (PackingMachineLayout.values num den input other)

omit [DecidableEq Extra] in
theorem general_updated_shape (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (baseRegister temporary : Other) (distinct : baseRegister ≠ temporary)
    (kind : PackingRegisterUpdate.Kind)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (htemporary : other temporary = 0) :
    registerTapes (updateSlots num den power baseRegister temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values (other baseRegister)
          (PackingRegisterUpdate.operation kind (other baseRegister) (input power))) =
      PackingMachineLayout.tapes num den base
        (Function.update input power
          (PackingRegisterUpdate.operation kind (other baseRegister) (input power))) other := by
  apply PackingRegisterFrame.replace (PackingMachineLayout.registers num den)
    (updateRegisters num den power baseRegister temporary distinct) base
    (PackingMachineLayout.values num den input other)
    (PackingMachineLayout.values num den
      (Function.update input power
        (PackingRegisterUpdate.operation kind (other baseRegister) (input power))) other)
    (PackingRegisterUpdate.values (other baseRegister)
      (PackingRegisterUpdate.operation kind (other baseRegister) (input power)))
  · intro r
    fin_cases r <;> simp [PackingRegisterUpdate.values, htemporary]
  · intro r hr
    have hrne : r ≠ PackingMachineLayout.inputs num den power := by
      intro heq
      apply hr
      refine ⟨1, ?_⟩
      simpa only [updateRegisters_one] using heq.symm
    simp only [PackingMachineLayout.values_update_input, Function.update_of_ne hrne]

theorem general_exec (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (baseRegister temporary : Other) (distinct : baseRegister ≠ temporary)
    (kind : PackingRegisterUpdate.Kind)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (htemporary : other temporary = 0)
    (state : PackingMachineBlocks.State) :
    ∃ steps ≤ 64 * ((other baseRegister).size + (input power).size + 1) ^ 2,
      Exec (PackingRegisterUpdate.code
          (updateSlots num den power baseRegister temporary distinct) kind)
        ⟨state, PackingMachineLayout.tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          PackingMachineLayout.tapes num den base
            (Function.update input power
              (PackingRegisterUpdate.operation kind (other baseRegister) (input power))) other⟩ := by
  obtain ⟨steps, hsteps, hrun⟩ := PackingRegisterUpdate.exec
    (updateSlots num den power baseRegister temporary distinct) kind
    (PackingMachineLayout.tapes num den base input other)
    (other baseRegister) (input power) state
  refine ⟨steps, hsteps, ?_⟩
  simpa only [general_shape num den power baseRegister temporary distinct base input other htemporary,
    general_updated_shape num den power baseRegister temporary distinct kind base input other
      htemporary] using hrun

end BinPackingGap.PackingVertexUpdate

end

end OAI

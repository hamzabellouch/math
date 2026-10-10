import OAI.Computability.BinPacking.Arithmetic.NatExpressionBranch
import OAI.Computability.BinPacking.Machines.GraphPackingBounds

namespace OAI

namespace BinPackingGap.BinaryRegisterProgram

section

open Turing
open BinPackingGames.Foundations.Complexity

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

noncomputable def addCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg)
    (labels : LocalLabel (.add op) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ label,
      p (labels label) = localInstruction slot (.add op) labels exit label)
    (base : K → List Bool) (values : Reg → Nat)
    (ready : commandReady (.add op) values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.add op))), BinaryAddMachine.clean ambient,
        registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (result (.add op) values)⟩)
      (cost (.add op) values) := by
  have hd : values op.destination = 0 := ready
  have run := BinaryAddPreserving.addInLinearTime (addSlots slot op) labels exit p
    (fun label => atLabels label) (registerTapes slot base values)
    (values op.left) (values op.right)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [hd]) (by simp) ambient
  have hresult : BinaryAddPreserving.resultTapes (addSlots slot op)
      (registerTapes slot base values) (values op.left) (values op.right) =
      registerTapes slot base (result (.add op) values) := by
    simpa only [BinaryAddPreserving.resultTapes, addSlots_five, result, destination, value]
      using registerTapes_update slot base values op.destination
        (values op.left + values op.right)
  simpa only [hresult, main, cost] using run

noncomputable def mulCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg)
    (labels : LocalLabel (.mul op) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ label,
      p (labels label) = localInstruction slot (.mul op) labels exit label)
    (base : K → List Bool) (values : Reg → Nat)
    (ready : commandReady (.mul op) values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.mul op))), BinaryAddMachine.clean ambient,
        registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (result (.mul op) values)⟩)
      (cost (.mul op) values) := by
  have hd : values op.destination = 0 := ready
  have hout : registerTapes slot base values (mulSlots slot op 2) = [] := by simp [hd]
  have run := BinaryMulMachine.multiplyNatInPolynomialTime (mulSlots slot op) labels exit p
    (fun label => atLabels label) (registerTapes slot base values)
    (values op.left) (values op.right) (by simp) (by simp)
    (registerTapes_mul_workspace slot op base values) ambient
  have hresult : Function.update (registerTapes slot base values) (mulSlots slot op 2)
      ((values op.left * values op.right).bits ++
        registerTapes slot base values (mulSlots slot op 2)) =
      registerTapes slot base (result (.mul op) values) := by
    rw [hout, List.append_nil, mulSlots_two]
    exact registerTapes_update slot base values op.destination
      (values op.left * values op.right)
  simpa only [hresult, main, cost, BinaryMulMachine.clean,
    BinaryAddMachine.clean, BinaryAddMachine.state, BinaryMulMachine.timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] using run

noncomputable def monusCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg)
    (labels : LocalLabel (.monus op) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ label,
      p (labels label) = localInstruction slot (.monus op) labels exit label)
    (base : K → List Bool) (values : Reg → Nat)
    (ready : commandReady (.monus op) values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.monus op))), BinaryAddMachine.clean ambient,
        registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (result (.monus op) values)⟩)
      (cost (.monus op) values) := by
  have hd : values op.destination = 0 := ready
  have hwork : ∀ i : Fin 7, 2 ≤ i.val →
      registerTapes slot base values (addSlots slot op i) = [] := by
    intro i hi
    by_cases hout : i = 5
    · subst i; simp [hd]
    · exact registerTapes_add_workspace slot op base values i hi hout
  have run := BinaryMonusPreserving.monusInLinearTime (addSlots slot op) labels exit p
    (fun label => atLabels label) (registerTapes slot base values)
    (values op.left) (values op.right) (by simp) (by simp) hwork ambient
  have hresult : BinaryMonusPreserving.resultTapes (addSlots slot op)
      (registerTapes slot base values) (values op.left) (values op.right) =
      registerTapes slot base (result (.monus op) values) := by
    simpa only [BinaryMonusPreserving.resultTapes, addSlots_five, result, destination, value]
      using registerTapes_update slot base values op.destination
        (values op.left - values op.right)
  simpa only [hresult, main, cost] using run

end

section

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open BinaryAddMachine (State clean)

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

noncomputable def constantCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (dst : Reg) (n : ℕ)
    (labels : LocalLabel (.constant dst n) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l,
      p (labels l) = localInstruction slot (.constant dst n) labels exit l)
    (base : K → List Bool) (vals : Reg → ℕ)
    (ready : commandReady (.constant dst n) vals) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.constant dst n))), clean ambient, registerTapes slot base vals⟩
      (some ⟨exit, clean ambient, registerTapes slot base (result (.constant dst n) vals)⟩)
      (cost (.constant dst n) vals) := by
  have hzero : vals dst = 0 := ready
  have hempty : registerTapes slot base vals (slot (.inl dst)) = [] := by
    simp only [registerTapes_reg, hzero, Nat.zero_bits]
  refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_rfl }
  change some (TM2.stepAux (p (labels ())) (clean ambient) (registerTapes slot base vals)) =
    some ⟨exit, clean ambient, registerTapes slot base (result (.constant dst n) vals)⟩
  rw [atLabels ()]
  simp only [localInstruction]
  rw [MachineSubstitution.stepAux_pushWord]
  simp only [List.reverse_reverse, hempty, List.append_nil, registerTapes_update]
  cases exit <;> rfl

noncomputable def clearCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (dst : Reg)
    (labels : LocalLabel (.clear dst) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, p (labels l) = localInstruction slot (.clear dst) labels exit l)
    (base : K → List Bool) (vals : Reg → ℕ)
    (_ready : commandReady (.clear dst) vals) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.clear dst))), clean ambient, registerTapes slot base vals⟩
      (some ⟨exit, clean ambient, registerTapes slot base (result (.clear dst) vals)⟩)
      (cost (.clear dst) vals) := by
  have run := MachineDrain.drainInTime (slot (.inl dst)) (labels ()) exit p
    (by simpa only [localInstruction] using atLabels ())
    (registerTapes slot base vals) ((ambient, false), none) none
  have hframe : Function.update (registerTapes slot base vals) (slot (.inl dst)) [] =
      registerTapes slot base (result (.clear dst) vals) := by
    simpa only [result, destination, value, Nat.zero_bits] using
      registerTapes_update slot base vals dst 0
  rw [hframe] at run
  simpa only [main, cost, BinaryAddMachine.clean, BinaryAddMachine.state,
    registerTapes_reg, Nat.size_eq_bits_len] using run

noncomputable def copyCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (dst src : Reg) (different : dst ≠ src)
    (labels : LocalLabel (.copy dst src different) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l,
      p (labels l) = localInstruction slot (.copy dst src different) labels exit l)
    (base : K → List Bool) (vals : Reg → ℕ)
    (ready : commandReady (.copy dst src different) vals) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.copy dst src different))), clean ambient,
        registerTapes slot base vals⟩
      (some ⟨exit, clean ambient,
        registerTapes slot base (result (.copy dst src different) vals)⟩)
      (cost (.copy dst src different) vals) := by
  have hzero : vals dst = 0 := ready
  have hSD : slot (.inl src) ≠ slot (.inl dst) :=
    slot.injective.ne (by simpa only [ne_eq, Sum.inl.injEq] using different.symm)
  have hSC : slot (.inl src) ≠ slot (.inr (0 : Fin 6)) :=
    slot.injective.ne (by simp)
  have hDC : slot (.inl dst) ≠ slot (.inr (0 : Fin 6)) :=
    slot.injective.ne (by simp)
  have run := MachineCopy.copyInTime (slot (.inl src)) (slot (.inl dst))
    (slot (.inr (0 : Fin 6))) hSD hSC hDC false (labels false) (labels true) exit p
    (by simpa [localInstruction] using atLabels false)
    (by simpa [localInstruction] using atLabels true)
    (registerTapes slot base vals) (by simp only [registerTapes_scratch])
    ((ambient, false), none) none
  have hframe : Function.update (registerTapes slot base vals) (slot (.inl dst))
      (registerTapes slot base vals (slot (.inl src)) ++
        registerTapes slot base vals (slot (.inl dst))) =
      registerTapes slot base (result (.copy dst src different) vals) := by
    simp only [registerTapes_reg, hzero, Nat.zero_bits, List.append_nil]
    exact registerTapes_update slot base vals dst (vals src)
  rw [hframe] at run
  simpa only [main, cost, BinaryAddMachine.clean, BinaryAddMachine.state,
    registerTapes_reg, Nat.size_eq_bits_len] using run

end

open Turing
open BinPackingGames.Foundations.Complexity

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

def appendRuns {X : Type} {step : X → Option X} {a b c : X} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) where
  steps := first.steps + second.steps
  evals_in_steps := by
    rw [Nat.add_comm, Function.iterate_add_apply, first.evals_in_steps]
    exact second.evals_in_steps
  steps_le_m := Nat.add_le_add first.steps_le_m second.steps_le_m

noncomputable def commandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (command : Command Reg)
    (labels : LocalLabel command → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ l, p (labels l) = localInstruction slot command labels exit l)
    (base : K → List Bool) (values : Reg → Nat) (ready : commandReady command values)
    (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main command)), BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient, registerTapes slot base (result command values)⟩)
      (cost command values) := by
  cases command with
  | add op => exact addCommandInTime slot op labels exit p atLabels base values ready ambient
  | mul op => exact mulCommandInTime slot op labels exit p atLabels base values ready ambient
  | monus op => exact monusCommandInTime slot op labels exit p atLabels base values ready ambient
  | constant dst n =>
      exact constantCommandInTime slot dst n labels exit p atLabels base values ready ambient
  | clear dst => exact clearCommandInTime slot dst labels exit p atLabels base values ready ambient
  | copy dst src different =>
      exact copyCommandInTime slot dst src different labels exit p atLabels base values ready ambient

noncomputable def runInTime (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (labels : Label commands → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ l, p (labels l) = instruction slot commands labels exit l)
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨entry commands labels exit, BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (resultOf commands values)⟩) (budget commands values) := by
  induction commands generalizing values with
  | nil => exact { steps := 0, evals_in_steps := rfl, steps_le_m := Nat.le_refl 0 }
  | cons command commands ih =>
      have firstRun := commandInTime slot command (fun l => labels (.inl l))
        (entry commands (fun l => labels (.inr l)) exit) p
        (fun l => atLabels (.inl l)) base values ready.1 ambient
      have tailRun := ih (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
        (result command values) ready.2
      exact appendRuns firstRun tailRun

def program (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg)) :
    Label commands → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) (Label commands)
      (BinaryAddMachine.State A) := instruction slot commands id none

noncomputable def programInTime (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (base : K → List Bool) (values : Reg → Nat)
    (ready : Ready commands values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program (A := A) slot commands))
      ⟨entry commands id none, BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨none, BinaryAddMachine.clean ambient,
        registerTapes slot base (resultOf commands values)⟩) (budget commands values) :=
  runInTime slot commands id none (program slot commands) (fun _ => rfl) base values ready ambient

def BitBounded (width : Nat) : List (Command Reg) → (Reg → Nat) → Prop
  | [], values => ∀ r, (values r).size ≤ width
  | command :: commands, values =>
      (∀ r, (values r).size ≤ width) ∧ BitBounded width commands (result command values)

def commandBound (width : Nat) : Nat := 16 * width ^ 2 + 28 * width + 12

omit [DecidableEq Reg] in
theorem cost_le (command : Command Reg) (values : Reg → Nat) (width : Nat)
    (bounded : ∀ r, (values r).size ≤ width) : cost command values ≤ commandBound width := by
  cases command with
  | add op =>
      have hl := bounded op.left
      have hr := bounded op.right
      simp only [cost, commandBound]
      omega
  | mul op =>
      have hsum : (values op.left).size + (values op.right).size ≤ 2 * width := by
        have hl := bounded op.left
        have hr := bounded op.right
        omega
      have hsquare := Nat.mul_le_mul hsum hsum
      simp only [cost, commandBound]
      nlinarith
  | monus op =>
      have hl := bounded op.left
      have hr := bounded op.right
      simp only [cost, commandBound]
      omega
  | constant dst n => simp only [cost, commandBound]; omega
  | clear dst =>
      have hd := bounded dst
      simp only [cost, commandBound]
      omega
  | copy dst src different =>
      have hs := bounded src
      simp only [cost, commandBound]
      omega

theorem budget_le (commands : List (Command Reg)) (values : Reg → Nat) (width : Nat)
    (bounded : BitBounded width commands values) :
    budget commands values ≤ commands.length * commandBound width := by
  induction commands generalizing values with
  | nil => simp [budget, MachineFiniteSequence.steps]
  | cons command commands ih =>
      have headBound := cost_le command values width bounded.1
      have tailBound := ih (result command values) bounded.2
      change cost command values + budget commands (result command values) ≤
        (commands.length + 1) * commandBound width
      calc
        _ ≤ commandBound width + commands.length * commandBound width :=
          Nat.add_le_add headBound tailBound
        _ = _ := by simp [Nat.add_mul, Nat.add_comm]

noncomputable def programInQuadraticTime (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (base : K → List Bool) (values : Reg → Nat)
    (ready : Ready commands values) (ambient : A) (width : Nat)
    (bounded : BitBounded width commands values) :
    StateTransition.EvalsToInTime (TM2.step (program (A := A) slot commands))
      ⟨entry commands id none, BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨none, BinaryAddMachine.clean ambient,
        registerTapes slot base (resultOf commands values)⟩)
      (commands.length * commandBound width) := by
  let run := programInTime slot commands base values ready ambient
  exact { steps := run.steps
          evals_in_steps := run.evals_in_steps
          steps_le_m := run.steps_le_m.trans (budget_le commands values width bounded) }

noncomputable def runInQuadraticTime (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (labels : Label commands → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ l, p (labels l) = instruction slot commands labels exit l)
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values)
    (ambient : A) (width : Nat) (bounded : BitBounded width commands values) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨entry commands labels exit, BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (resultOf commands values)⟩)
      (commands.length * commandBound width) := by
  let run := runInTime slot commands labels exit p atLabels base values ready ambient
  exact { steps := run.steps
          evals_in_steps := run.evals_in_steps
          steps_le_m := run.steps_le_m.trans (budget_le commands values width bounded) }

end BinPackingGap.BinaryRegisterProgram

namespace BinPackingGap.NatExpressionCompiler

open BinaryRegisterProgram

variable {α Reg : Type} [DecidableEq Reg]

def compileInto (inputs : α → Reg) :
    (expression : Expr α) → (nodes : Node expression ↪ Reg) →
      (∀ a node, inputs a ≠ nodes node) → List (Command Reg)
  | .constant n, nodes, _ => [.constant (nodes ()) n]
  | .input a, nodes, apart => [.copy (nodes ()) (inputs a) (apart a ()).symm]
  | .add left right, nodes, apart =>
      (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))) ++
      compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node)))) ++
      [command .add (branchOperands nodes (root left) (root right))]
  | .mul left right, nodes, apart =>
      (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))) ++
      compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node)))) ++
      [command .mul (branchOperands nodes (root left) (root right))]
  | .monus left right, nodes, apart =>
      (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))) ++
      compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node)))) ++
      [command .monus (branchOperands nodes (root left) (root right))]

theorem compileInto_correct (inputs : α → Reg) (expression : Expr α)
    (nodes : Node expression ↪ Reg) (apart : ∀ a node, inputs a ≠ nodes node) :
    Correct inputs nodes (root expression) (fun values => eval values expression)
      (compileInto inputs expression nodes apart) := by
  induction expression with
  | constant n =>
      intro values empty
      refine ⟨?_, ?_, ?_⟩
      · change values (nodes ()) = 0 ∧ True
        exact ⟨empty (), trivial⟩
      · simp [compileInto, result, destination, value]
      · intro r outside
        simpa only [compileInto, resultOf_cons, resultOf_nil] using
          result_other (.constant (nodes ()) n) values r (outside ())
  | input a =>
      intro values empty
      refine ⟨?_, ?_, ?_⟩
      · change values (nodes ()) = 0 ∧ True
        exact ⟨empty (), trivial⟩
      · simp [compileInto, result, destination, value]
      · intro r outside
        simpa only [compileInto, resultOf_cons, resultOf_nil] using
          result_other (.copy (nodes ()) (inputs a) (apart a ()).symm) values r (outside ())
  | add left right ihLeft ihRight =>
      exact branchCorrect .add inputs nodes apart (root left) (root right)
        (fun values => eval values left) (fun values => eval values right)
        (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
        (ihLeft (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (ihRight (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
  | mul left right ihLeft ihRight =>
      exact branchCorrect .mul inputs nodes apart (root left) (root right)
        (fun values => eval values left) (fun values => eval values right)
        (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
        (ihLeft (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (ihRight (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
  | monus left right ihLeft ihRight =>
      exact branchCorrect .monus inputs nodes apart (root left) (root right)
        (fun values => eval values left) (fun values => eval values right)
        (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
        (ihLeft (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (ihRight (rightReg nodes) (fun a node => apart a (.inr (.inr node))))

abbrev Register (expression : Expr α) := α ⊕ Node expression

def inputRegister (expression : Expr α) : α → Register expression := Sum.inl

def nodeRegister (expression : Expr α) : Node expression ↪ Register expression where
  toFun := Sum.inr
  inj' := by
    intro a b h
    exact Sum.inr.inj h

theorem registers_disjoint (expression : Expr α) (a : α) (node : Node expression) :
    inputRegister expression a ≠ nodeRegister expression node := by
  simp [inputRegister, nodeRegister]

def initialValues (expression : Expr α) (values : α → Nat) : Register expression → Nat
  | .inl a => values a
  | .inr _ => 0

variable [DecidableEq α]

def commands (expression : Expr α) : List (Command (Register expression)) :=
  compileInto (inputRegister expression) expression (nodeRegister expression)
    (registers_disjoint expression)

theorem commands_correct (expression : Expr α) :
    Correct (inputRegister expression) (nodeRegister expression) (root expression)
      (fun values => eval values expression) (commands expression) :=
  compileInto_correct _ _ _ _

theorem commands_ready (expression : Expr α) (values : α → Nat) :
    Ready (commands expression) (initialValues expression values) := by
  have h := commands_correct expression (initialValues expression values) (fun _ => rfl)
  exact h.1

theorem commands_output (expression : Expr α) (values : α → Nat) :
    resultOf (commands expression) (initialValues expression values)
      (nodeRegister expression (root expression)) = eval values expression := by
  have h := commands_correct expression (initialValues expression values) (fun _ => rfl)
  simpa only [inputRegister, initialValues] using h.2.1

theorem commands_preserve_input (expression : Expr α) (values : α → Nat) (a : α) :
    resultOf (commands expression) (initialValues expression values)
      (inputRegister expression a) = values a := by
  have h := commands_correct expression (initialValues expression values) (fun _ => rfl)
  exact h.2.2 (inputRegister expression a) (registers_disjoint expression a)

noncomputable def compiledProgramInTime {K A : Type} [DecidableEq K]
    (expression : Expr α) (slot : (Register expression ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : α → Nat) (ambient : A) :
    StateTransition.EvalsToInTime
      (Turing.TM2.step (BinaryRegisterProgram.program (A := A) slot (commands expression)))
      ⟨BinaryRegisterProgram.entry (commands expression) id none,
        BinaryAddMachine.clean ambient,
        registerTapes slot base (initialValues expression values)⟩
      (some ⟨none, BinaryAddMachine.clean ambient,
        registerTapes slot base
          (resultOf (commands expression) (initialValues expression values))⟩)
      (budget (commands expression) (initialValues expression values)) :=
  BinaryRegisterProgram.programInTime slot (commands expression) base
    (initialValues expression values) (commands_ready expression values) ambient

theorem compiled_output_tape {K : Type} (expression : Expr α)
    (slot : (Register expression ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (values : α → Nat) :
    registerTapes slot base (resultOf (commands expression) (initialValues expression values))
      (slot (.inl (nodeRegister expression (root expression)))) =
      (eval values expression).bits := by
  rw [registerTapes_reg, commands_output]

theorem compiled_input_tape {K : Type} (expression : Expr α)
    (slot : (Register expression ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (values : α → Nat) (a : α) :
    registerTapes slot base (resultOf (commands expression) (initialValues expression values))
      (slot (.inl (inputRegister expression a))) = (values a).bits := by
  rw [registerTapes_reg, commands_preserve_input]

end BinPackingGap.NatExpressionCompiler

namespace BinPackingGap.BinaryRegisterProgram

open Turing
open BinPackingGames.Foundations.Complexity

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

def constantSize : Command Reg → Nat
  | .constant _ n => n.size
  | _ => 0

def maxConstantSize : List (Command Reg) → Nat
  | [] => 0
  | command :: commands => max (constantSize command) (maxConstantSize commands)

omit [DecidableEq Reg] in
theorem constantSize_le_maxConstantSize (commands : List (Command Reg))
    (command : Command Reg) (member : command ∈ commands) :
    constantSize command ≤ maxConstantSize commands := by
  induction commands with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | ht
      · exact Nat.le_max_left _ _
      · exact (ih ht).trans (Nat.le_max_right _ _)

theorem result_size_le (command : Command Reg) (values : Reg → Nat) (width : Nat)
    (positive : 0 < width) (initial : ∀ r, (values r).size ≤ width)
    (literal : constantSize command ≤ width) :
    ∀ r, (result command values r).size ≤ 2 * width := by
  have hv : (value command values).size ≤ 2 * width := by
    cases command with
    | add op =>
        have ha := nat_size_add_le_max (values op.left) (values op.right)
        have hl := initial op.left
        have hr := initial op.right
        change (values op.left + values op.right).size ≤ 2 * width
        omega
    | mul op =>
        have hm := nat_size_mul_le (values op.left) (values op.right)
        have hl := initial op.left
        have hr := initial op.right
        change (values op.left * values op.right).size ≤ 2 * width
        omega
    | monus op =>
        have hm := nat_size_sub_le (values op.left) (values op.right)
        have hl := initial op.left
        change (values op.left - values op.right).size ≤ 2 * width
        omega
    | constant dst n =>
        change n.size ≤ width at literal
        change n.size ≤ 2 * width
        omega
    | clear dst => simp [value, Nat.size_zero]
    | copy dst src different =>
        have hs := initial src
        change (values src).size ≤ 2 * width
        omega
  intro r
  by_cases heq : r = destination command
  · subst r
    simpa only [result_destination] using hv
  · rw [result_other command values r heq]
    exact (initial r).trans (by omega)

theorem bitBounded_of_positive_width (commands : List (Command Reg))
    (values : Reg → Nat) (width : Nat) (positive : 0 < width)
    (initial : ∀ r, (values r).size ≤ width)
    (constants : ∀ command ∈ commands, constantSize command ≤ width) :
    BitBounded (2 ^ commands.length * width) commands values := by
  induction commands generalizing values width with
  | nil => simpa [BitBounded] using initial
  | cons command commands ih =>
      have nextInitial := result_size_le command values width positive initial
        (constants command (by simp))
      have nextConstants : ∀ c ∈ commands, constantSize c ≤ 2 * width := by
        intro c hc
        have h := constants c (by simp [hc])
        omega
      have tailBound := ih (result command values) (2 * width) (by omega)
        nextInitial nextConstants
      have scale : 2 ^ commands.length * (2 * width) =
          2 ^ (commands.length + 1) * width := by
        rw [Nat.pow_succ]
        ring
      change (∀ r, (values r).size ≤ 2 ^ (commands.length + 1) * width) ∧ _
      constructor
      · intro r
        have hp : 0 < (2 : Nat) ^ (commands.length + 1) := pow_pos (by decide) _
        have hr := initial r
        nlinarith
      · simpa only [scale, List.length_cons] using tailBound

def staticWidth (commands : List (Command Reg)) (inputWidth : Nat) : Nat :=
  2 ^ commands.length * (inputWidth + maxConstantSize commands + 1)

theorem bitBounded_from_input (commands : List (Command Reg)) (values : Reg → Nat)
    (inputWidth : Nat) (initial : ∀ r, (values r).size ≤ inputWidth) :
    BitBounded (staticWidth commands inputWidth) commands values := by
  apply bitBounded_of_positive_width commands values
    (inputWidth + maxConstantSize commands + 1)
  · omega
  · intro r
    have hr := initial r
    omega
  · intro command hc
    have h := constantSize_le_maxConstantSize commands command hc
    omega

noncomputable def runtimePolynomial (commands : List (Command Reg)) : Polynomial Nat :=
  let scale : Polynomial Nat := Polynomial.C (2 ^ commands.length) *
    (Polynomial.X + Polynomial.C (maxConstantSize commands + 1))
  Polynomial.C commands.length *
    (Polynomial.C 16 * scale ^ 2 + Polynomial.C 28 * scale + Polynomial.C 12)

omit [DecidableEq Reg] in
theorem runtimePolynomial_eval (commands : List (Command Reg)) (inputWidth : Nat) :
    (runtimePolynomial commands).eval inputWidth =
      commands.length * commandBound (staticWidth commands inputWidth) := by
  simp only [runtimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, commandBound, staticWidth]
  ring

noncomputable def programInPolynomialTime (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (base : K → List Bool) (values : Reg → Nat)
    (ready : Ready commands values) (ambient : A) (inputWidth : Nat)
    (initial : ∀ r, (values r).size ≤ inputWidth) :
    StateTransition.EvalsToInTime (TM2.step (program (A := A) slot commands))
      ⟨entry commands id none, BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨none, BinaryAddMachine.clean ambient,
        registerTapes slot base (resultOf commands values)⟩)
      ((runtimePolynomial commands).eval inputWidth) := by
  rw [runtimePolynomial_eval]
  exact programInQuadraticTime slot commands base values ready ambient
    (staticWidth commands inputWidth) (bitBounded_from_input commands values inputWidth initial)

noncomputable def runInPolynomialTime (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (labels : Label commands → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ l, p (labels l) = instruction slot commands labels exit l)
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values)
    (ambient : A) (inputWidth : Nat) (initial : ∀ r, (values r).size ≤ inputWidth) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨entry commands labels exit, BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (resultOf commands values)⟩)
      ((runtimePolynomial commands).eval inputWidth) := by
  rw [runtimePolynomial_eval]
  exact runInQuadraticTime slot commands labels exit p atLabels base values ready ambient
    (staticWidth commands inputWidth) (bitBounded_from_input commands values inputWidth initial)

end BinPackingGap.BinaryRegisterProgram

namespace BinPackingGap.NatExpressionCompiler

open Turing
open BinaryRegisterProgram

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem initialValues_size_le (expression : Expr α) (values : α → Nat) (width : Nat)
    (inputBound : ∀ a, (values a).size ≤ width) :
    ∀ r, (initialValues expression values r).size ≤ width := by
  intro r
  cases r with
  | inl a => exact inputBound a
  | inr node => simp [initialValues]

noncomputable def timePolynomial (expression : Expr α) : Polynomial Nat :=
  runtimePolynomial (commands expression)

def outputWidth (expression : Expr α) (inputWidth : Nat) : Nat :=
  staticWidth (commands expression) inputWidth

private theorem final_size_le {Reg : Type} [DecidableEq Reg]
    (program : List (Command Reg)) (values : Reg → Nat) (width : Nat)
    (bounded : BitBounded width program values) :
    ∀ r, (resultOf program values r).size ≤ width := by
  induction program generalizing values with
  | nil => exact bounded
  | cons command program ih =>
      exact ih (result command values) bounded.2

theorem eval_size_le (expression : Expr α) (values : α → Nat) (inputWidth : Nat)
    (inputBound : ∀ a, (values a).size ≤ inputWidth) :
    (eval values expression).size ≤ outputWidth expression inputWidth := by
  have bounded := bitBounded_from_input (commands expression)
    (initialValues expression values) inputWidth
    (initialValues_size_le expression values inputWidth inputBound)
  have final := final_size_le (commands expression) (initialValues expression values)
    (outputWidth expression inputWidth) bounded
    (nodeRegister expression (root expression))
  simpa only [commands_output] using final

noncomputable def compiledProgramInPolynomialTime {K A : Type} [DecidableEq K]
    (expression : Expr α) (slot : (Register expression ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : α → Nat) (ambient : A) (inputWidth : Nat)
    (inputBound : ∀ a, (values a).size ≤ inputWidth) :
    StateTransition.EvalsToInTime
      (TM2.step (BinaryRegisterProgram.program (A := A) slot (commands expression)))
      ⟨BinaryRegisterProgram.entry (commands expression) id none,
        BinaryAddMachine.clean ambient,
        registerTapes slot base (initialValues expression values)⟩
      (some ⟨none, BinaryAddMachine.clean ambient,
        registerTapes slot base
          (resultOf (commands expression) (initialValues expression values))⟩)
      ((timePolynomial expression).eval inputWidth) :=
  BinaryRegisterProgram.programInPolynomialTime slot (commands expression) base
    (initialValues expression values) (commands_ready expression values) ambient inputWidth
    (initialValues_size_le expression values inputWidth inputBound)

noncomputable def compiledRunInPolynomialTime {K Λ A : Type} [DecidableEq K]
    (expression : Expr α) (slot : (Register expression ⊕ Fin 6) ↪ K)
    (labels : BinaryRegisterProgram.Label (commands expression) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ label, p (labels label) =
      BinaryRegisterProgram.instruction slot (commands expression) labels exit label)
    (base : K → List Bool) (values : α → Nat) (ambient : A) (inputWidth : Nat)
    (inputBound : ∀ a, (values a).size ≤ inputWidth) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨BinaryRegisterProgram.entry (commands expression) labels exit,
        BinaryAddMachine.clean ambient,
        registerTapes slot base (initialValues expression values)⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base
          (resultOf (commands expression) (initialValues expression values))⟩)
      ((timePolynomial expression).eval inputWidth) :=
  BinaryRegisterProgram.runInPolynomialTime slot (commands expression) labels exit p atLabels
    base (initialValues expression values) (commands_ready expression values) ambient inputWidth
    (initialValues_size_le expression values inputWidth inputBound)

end BinPackingGap.NatExpressionCompiler

end OAI

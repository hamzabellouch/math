import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Arithmetic.BinaryToTallyMachine
import OAI.Computability.BinPacking.Arithmetic.ResetExpressionCompiler
import OAI.Computability.BinPacking.Inventory.InventoryScores

namespace OAI

noncomputable section

namespace BinPackingGap.PackingSetupExpression

section

open NatExpressionCompiler

structure Parameters where
  P : Nat
  K : Nat
  d : Nat
  tPlus : Nat
  tMinus : Nat

inductive Input
  | n | m | k
  deriving DecidableEq

protected abbrev Input.enumList : List Input := [.n, .m, .k]

protected theorem Input.enumList_getElem?_ctorIdx_eq (x : Input) :
    Input.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Input.enumList_nodup : Input.enumList.Nodup := by decide

instance : Fintype Input where
  elems := ⟨Input.enumList, Input.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Output
  | repetitions | base | edgeRepetitions | bins
  | upOne | upZero | umOne | umZero | edgeStock
  | treeFlags | jobFlags | one | three
  deriving DecidableEq

protected abbrev Output.enumList : List Output := [.repetitions, .base, .edgeRepetitions, .bins,
  .upOne, .upZero, .umOne, .umZero, .edgeStock, .treeFlags, .jobFlags, .one, .three]

protected theorem Output.enumList_getElem?_ctorIdx_eq (x : Output) :
    Output.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Output.enumList_nodup : Output.enumList.Nodup := by decide

instance : Fintype Output where
  elems := ⟨Output.enumList, Output.enumList_nodup⟩
  complete x := by cases x <;> decide

def inputs (n m k : Nat) : Input → Nat
  | .n => n
  | .m => m
  | .k => k

def repetitions (p : Parameters) : Expr Input :=
  .mul (.constant 100) (.add (.add (.constant p.P)
    (.mul (.input .n) (.constant p.K))) (.constant 1))

def edgeRepetitions (p : Parameters) : Expr Input :=
  .mul (.input .m) (repetitions p)

def jobFlags (p : Parameters) : Expr Input :=
  .mul (.constant (2 * p.d)) (edgeRepetitions p)

def expression (p : Parameters) : Output → Expr Input
  | .repetitions => repetitions p
  | .base => .add (repetitions p) (.constant 1)
  | .edgeRepetitions => edgeRepetitions p
  | .bins => .add (.mul (.input .n) (.constant (p.tPlus + p.tMinus)))
      (.mul (.constant (4 * p.d)) (edgeRepetitions p))
  | .upOne => .mul (.constant p.d) (.input .k)
  | .upZero => .monus (.add (.mul (.input .n) (.constant p.tPlus)) (jobFlags p))
      (.mul (.constant p.d) (.input .k))
  | .umOne => .mul (.constant p.d) (.monus (.input .n) (.input .k))
  | .umZero => .monus (.mul (.input .n) (.constant p.tMinus))
      (.mul (.constant p.d) (.monus (.input .n) (.input .k)))
  | .edgeStock => .mul (.constant p.d) (repetitions p)
  | .treeFlags => .mul (.input .n) (.constant (p.tPlus + p.tMinus))
  | .jobFlags => jobFlags p
  | .one => .constant 1
  | .three => .constant 3

def outputValues (p : Parameters) (n m k : Nat) : Output → Nat
  | .repetitions => 100 * (p.P + n * p.K + 1)
  | .base => 100 * (p.P + n * p.K + 1) + 1
  | .edgeRepetitions => m * (100 * (p.P + n * p.K + 1))
  | .bins => n * (p.tPlus + p.tMinus) +
      (4 * p.d) * (m * (100 * (p.P + n * p.K + 1)))
  | .upOne => p.d * k
  | .upZero => n * p.tPlus + (2 * p.d) * (m * (100 * (p.P + n * p.K + 1))) - p.d * k
  | .umOne => p.d * (n - k)
  | .umZero => n * p.tMinus - p.d * (n - k)
  | .edgeStock => p.d * (100 * (p.P + n * p.K + 1))
  | .treeFlags => n * (p.tPlus + p.tMinus)
  | .jobFlags => (2 * p.d) * (m * (100 * (p.P + n * p.K + 1)))
  | .one => 1
  | .three => 3

theorem eval_expression (p : Parameters) (n m k : Nat) (o : Output) :
    eval (inputs n m k) (expression p o) = outputValues p n m k o := by
  cases o <;> rfl

end

def inventoryOutput (D : InventoryData) : Output → Nat
  | .repetitions => D.R
  | .base => D.R + 1
  | .edgeRepetitions => D.graph.edges.length * D.R
  | .bins => D.B
  | .upOne => D.globalStock (.up true)
  | .upZero => D.globalStock (.up false)
  | .umOne => D.globalStock (.um true)
  | .umZero => D.globalStock (.um false)
  | .edgeStock => D.d * D.R
  | .treeFlags => D.flagStock .tree
  | .jobFlags => D.flagStock .main
  | .one => 1
  | .three => 3

theorem outputValues_eq_inventory (p : Parameters) (D : InventoryData)
    (hd : p.d = D.d) (hplus : p.tPlus = D.tPlus) (hminus : p.tMinus = D.tMinus)
    (hR : D.R = 100 * (p.P + D.graph.n * p.K + 1)) :
    outputValues p D.graph.n D.graph.edges.length D.k = inventoryOutput D := by
  funext o
  cases o <;>
    simp [outputValues, inventoryOutput, ← hR, hd, hplus, hminus,
      InventoryData.globalStock, InventoryData.flagStock, InventoryData.minusSlots,
      InventoryData.treeFlags, InventoryData.jobFlags, D.B_closed, D.plusSlots_eq,
      D.sum_J, InventoryData.t, Nat.mul_assoc]

end BinPackingGap.PackingSetupExpression

namespace BinPackingGap.PackingSetupMachine

section

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram
open PackingSetupExpression

abbrev Reg (p : Parameters) := Input ⊕ (Output ⊕ (Σ o : Output, Node (expression p o)))

def input (p : Parameters) : Input → Reg p := Sum.inl
def output (p : Parameters) (o : Output) : Reg p := .inr (.inl o)

def nodes (p : Parameters) (o : Output) : Node (expression p o) ↪ Reg p where
  toFun n := .inr (.inr ⟨o, n⟩)
  inj' := by
    intro a b h
    have hs := Sum.inr.inj (Sum.inr.inj h)
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hs

def frame (p : Parameters) (ins : Input → Nat) (outs : Output → Nat) : Reg p → Nat
  | .inl a => ins a
  | .inr (.inl o) => outs o
  | .inr (.inr _) => 0

theorem frame_update (p : Parameters) (ins : Input → Nat) (outs : Output → Nat)
    (o : Output) (v : Nat) :
    Function.update (frame p ins outs) (output p o) v =
      frame p ins (Function.update outs o v) := by
  funext r
  rcases r with a | (q | n)
  · simp [frame, output]
  · by_cases h : q = o <;> simp [frame, output, h]
  · simp [frame, output]

def block (p : Parameters) (o : Output) : List (Command (Reg p)) :=
  ResetExpressionCompiler.commands (input p) (expression p o) (nodes p o)
    (by intros; simp [input, nodes]) (output p o) (by
      intro n equal
      change (Sum.inr (Sum.inl o) : Reg p) = Sum.inr (Sum.inr ⟨o, n⟩) at equal
      cases Sum.inr.inj equal)

theorem block_correct (p : Parameters) (o : Output)
    (ins : Input → Nat) (outs : Output → Nat) :
    Ready (block p o) (frame p ins outs) ∧
      resultOf (block p o) (frame p ins outs) =
        frame p ins (Function.update outs o (eval ins (expression p o))) := by
  have h := ResetExpressionCompiler.correct (input p) (expression p o) (nodes p o)
    (by intros; simp [input, nodes]) (output p o) (by
      intro n equal
      change (Sum.inr (Sum.inl o) : Reg p) = Sum.inr (Sum.inr ⟨o, n⟩) at equal
      cases Sum.inr.inj equal)
    (by intros; simp [input, output]) (frame p ins outs) (fun _ => rfl)
  refine ⟨h.1, ?_⟩
  calc
    resultOf (block p o) (frame p ins outs) =
        Function.update (frame p ins outs) (output p o) (eval ins (expression p o)) := by
      simpa only [block, input, frame] using h.2
    _ = _ := frame_update p ins outs o _

def outputOrder : List Output :=
  [.repetitions, .base, .edgeRepetitions, .bins, .upOne, .upZero,
    .umOne, .umZero, .edgeStock, .treeFlags, .jobFlags, .one, .three]

theorem mem_outputOrder (o : Output) : o ∈ outputOrder := by
  cases o <;> simp [outputOrder]

def commandsFor (p : Parameters) (order : List Output) : List (Command (Reg p)) :=
  order.flatMap (block p)

def outputsAfter (p : Parameters) (ins : Input → Nat) :
    List Output → (Output → Nat) → Output → Nat
  | [], outs => outs
  | o :: tail, outs => outputsAfter p ins tail
      (Function.update outs o (eval ins (expression p o)))

theorem outputsAfter_eq (p : Parameters) (ins : Input → Nat) (order : List Output)
    (outs : Output → Nat) (o : Output) :
    outputsAfter p ins order outs o =
      if o ∈ order then eval ins (expression p o) else outs o := by
  induction order generalizing outs with
  | nil => simp [outputsAfter]
  | cons q tail ih =>
      rw [outputsAfter, ih]
      by_cases ht : o ∈ tail
      · simp [ht]
      · by_cases he : o = q
        · subst o; simp [ht]
        · simp [ht, he]

theorem commandsFor_correct (p : Parameters) (order : List Output)
    (ins : Input → Nat) (outs : Output → Nat) :
    Ready (commandsFor p order) (frame p ins outs) ∧
      resultOf (commandsFor p order) (frame p ins outs) =
        frame p ins (outputsAfter p ins order outs) := by
  induction order generalizing outs with
  | nil => exact ⟨True.intro, rfl⟩
  | cons o tail ih =>
      have head := block_correct p o ins outs
      have rest := ih (Function.update outs o (eval ins (expression p o)))
      constructor
      · change Ready (block p o ++ commandsFor p tail) (frame p ins outs)
        rw [Ready_append, head.2]
        exact ⟨head.1, rest.1⟩
      · change resultOf (block p o ++ commandsFor p tail) (frame p ins outs) = _
        rw [resultOf_append, head.2]
        exact rest.2

def commands (p : Parameters) := commandsFor p outputOrder

theorem commands_correct (p : Parameters) (n m k : Nat) :
    Ready (commands p) (frame p (inputs n m k) (fun _ => 0)) ∧
      resultOf (commands p) (frame p (inputs n m k) (fun _ => 0)) =
        frame p (inputs n m k) (outputValues p n m k) := by
  have h := commandsFor_correct p outputOrder (inputs n m k) (fun _ => 0)
  refine ⟨h.1, h.2.trans ?_⟩
  congr 1
  funext o
  rw [outputsAfter_eq, ite_eq_left (mem_outputOrder o), eval_expression]

variable {K A : Type} [DecidableEq K]

def code (p : Parameters) (slot : (Reg p ⊕ Fin 6) ↪ K) :
    Code (K := K) (S := BinaryAddMachine.State A) :=
  BinaryRegisterStructured.code slot (commands p)

def timePolynomial (p : Parameters) : Polynomial Nat :=
  runtimePolynomial (commands p) + Polynomial.C 1

theorem exec (p : Parameters) (slot : (Reg p ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (n m k width : Nat)
    (hn : n.size ≤ width) (hm : m.size ≤ width) (hk : k.size ≤ width)
    (ambient : A) :
    ∃ steps ≤ (timePolynomial p).eval width,
      Exec (code p slot)
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot base (frame p (inputs n m k) (fun _ => 0))⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot base (frame p (inputs n m k) (outputValues p n m k))⟩ := by
  have hwidth : ∀ r, (frame p (inputs n m k) (fun _ => 0) r).size ≤ width := by
    intro r
    rcases r with a | (o | temp)
    · cases a
      · exact hn
      · exact hm
      · exact hk
    · simp [frame]
    · simp [frame]
  have correct := commands_correct p n m k
  obtain ⟨steps, bound, run⟩ := BinaryRegisterStructured.exec_polynomial slot (commands p)
    base (frame p (inputs n m k) (fun _ => 0)) correct.1 ambient width hwidth
  refine ⟨steps, ?_, ?_⟩
  · simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_C] using bound
  · rw [correct.2] at run
    exact run

end

open BinaryRegisterProgram FiniteTapeProgram PackingSetupExpression

theorem exec_graph {K A : Type} [DecidableEq K]
    (p : Parameters) (slot : (Reg p ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (x : GraphReductionInput) (ambient : A) :
    ∃ steps ≤ (timePolynomial p).eval (graphBits x).length,
      Exec (code p slot)
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot base
            (frame p (inputs x.graph.n x.graph.edges.length x.k) (fun _ => 0))⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot base
            (frame p (inputs x.graph.n x.graph.edges.length x.k)
              (outputValues p x.graph.n x.graph.edges.length x.k))⟩ :=
  exec p slot base x.graph.n x.graph.edges.length x.k (graphBits x).length
    ((nat_size_le_self x.graph.n).trans (graph_vertexCount_le_bits x))
    ((nat_size_le_self x.graph.edges.length).trans (graph_edgeCount_le_bits x))
    ((nat_size_le_self x.k).trans (x.k_le.trans (graph_vertexCount_le_bits x))) ambient

end BinPackingGap.PackingSetupMachine

end

end OAI

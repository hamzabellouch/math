import Mathlib.Data.List.FinRange
import OAI.Computability.BinPacking.Inventory.PackingInventoryDescriptors
import OAI.Computability.BinPacking.Machines.PackingVertexUpdate

namespace OAI

noncomputable section

section

namespace BinPackingGap.NatExpressionCompiler

variable {α β : Type}

def substitute (replacement : α → Expr β) : Expr α → Expr β
  | .constant n => .constant n
  | .input a => replacement a
  | .add a b => .add (substitute replacement a) (substitute replacement b)
  | .mul a b => .mul (substitute replacement a) (substitute replacement b)
  | .monus a b => .monus (substitute replacement a) (substitute replacement b)

theorem eval_substitute (replacement : α → Expr β) (values : β → Nat) (e : Expr α) :
    eval values (substitute replacement e) = eval (fun a => eval values (replacement a)) e := by
  induction e <;> simp_all [substitute, eval]

def rename (f : α → β) : Expr α → Expr β := substitute (fun a => .input (f a))

theorem eval_rename (f : α → β) (values : β → Nat) (e : Expr α) :
    eval values (rename f e) = eval (values ∘ f) e := by
  simpa only [rename, eval_input, Function.comp_def] using
    eval_substitute (fun a => .input (f a)) values e

end BinPackingGap.NatExpressionCompiler

namespace BinPackingGap.PackingItemExpression

open NatExpressionCompiler

inductive Variable
  | vertexPower | geometry | labelPower | totalPower | edgePower | repetitionOne
  deriving DecidableEq

instance : Fintype Variable where
  elems := {.vertexPower, .geometry, .labelPower, .totalPower, .edgePower, .repetitionOne}
  complete v := by cases v <;> simp

def coordinateVariable : PackingCoordinateExpression.Input → Variable
  | .geometryDg => .geometry
  | .totalPowerA => .totalPower
  | .edgePower => .edgePower
  | .repetitionOne => .repetitionOne

def scalarReplacement (coordinate : PackingCoordinateExpression.Parts) :
    PackingScalarExpression.Variable → Expr Variable
  | .vertexPower => .input .vertexPower
  | .geometry => .input .geometry
  | .labelPower => .input .labelPower
  | .coordinatePositive => rename coordinateVariable coordinate.pos
  | .coordinateNegative => rename coordinateVariable coordinate.neg

def numerator (subclass : Subclass) (coordinate : PackingCoordinateExpression.Parts) :
    Expr Variable := substitute (scalarReplacement coordinate)
      (PackingScalarExpression.numerator subclass)

def denominator : Expr Variable :=
  .mul (.mul (.constant (10 ^ 9 * primaryBound))
    (.input .vertexPower)) (.input .geometry)

def values (D : InventoryData) (i : D.Item) : Variable → Nat
  | .vertexPower => 3 ^ D.graph.n
  | .geometry => D.coordinateDenominator
  | .labelPower => NaturalPackingNumerator.labelPower (D.itemLabel i)
  | .totalPower => PackingCoordinateExpression.coordinateValues D i .totalPowerA
  | .edgePower => PackingCoordinateExpression.coordinateValues D i .edgePower
  | .repetitionOne => PackingCoordinateExpression.coordinateValues D i .repetitionOne

theorem values_coordinateVariable (D : InventoryData) (i : D.Item) :
    values D i ∘ coordinateVariable = PackingCoordinateExpression.coordinateValues D i := by
  funext v
  cases v <;> rfl

def itemCoordinate (D : InventoryData) (i : D.Item) : PackingCoordinateExpression.Parts :=
  PackingCoordinateExpression.expression D.geometryBound
    (PackingCoordinateExpression.coordinateDescriptor D i)

theorem replacement_values (D : InventoryData) (i : D.Item) :
    (fun v => eval (values D i) (scalarReplacement (itemCoordinate D i) v)) =
      PackingScalarExpression.values D.coordinateDenominator (D.itemLabel i)
        (NaturalPackingNumerator.coordinateParts D i) := by
  funext v
  cases v with
  | vertexPower => rfl
  | geometry => rfl
  | labelPower => rfl
  | coordinatePositive =>
    simp only [scalarReplacement, eval_rename, values_coordinateVariable]
    exact PackingCoordinateExpression.eval_coordinate_pos D i
  | coordinateNegative =>
    simp only [scalarReplacement, eval_rename, values_coordinateVariable]
    exact PackingCoordinateExpression.eval_coordinate_neg D i

theorem eval_item_numerator (D : InventoryData) (i : D.Item) :
    eval (values D i) (numerator (D.itemSubclass i) (itemCoordinate D i)) =
      (D.itemRawPair i).1 := by
  rw [numerator, eval_substitute, replacement_values]
  exact PackingScalarExpression.eval_item_numerator D i

theorem eval_item_denominator (D : InventoryData) (i : D.Item) :
    eval (values D i) denominator = (D.itemRawPair i).2 := rfl

end BinPackingGap.PackingItemExpression

end

namespace BinPackingGap.PackingItemBlockMachine

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler
open PairExpressionCompiler

variable {α K A : Type} [DecidableEq α] [DecidableEq K]

def code (num den : Expr α) (slot : (Reg num den ⊕ Fin 6) ↪ K) (output : K) :
    Code (K := K) (S := BinaryAddMachine.State A) :=
  .seq (BinaryRegisterStructured.code slot (commands num den))
    (.seq (.atom (.push output (fun _ => true) .done))
      (.seq (RegisterFrameEmission.code (slot (.inl (numRoot num den))) output)
        (.seq (RegisterFrameEmission.code (slot (.inl (denRoot num den))) output)
          (BinaryRegisterStructured.code slot (clearCommands num den)))))

def record (num den : Expr α) (values : α → Nat) : List Bool :=
  true :: (BinaryEncoding.natBits (eval values num) ++ BinaryEncoding.natBits (eval values den))

def outputTapes (output : K) (base : K → List Bool) (word : List Bool) : K → List Bool :=
  Function.update base output (word.reverse ++ base output)

def widthPolynomial (num den : Expr α) : Polynomial Nat :=
  Polynomial.C (2 ^ (commands num den).length) *
    (Polynomial.X + Polynomial.C (maxConstantSize (commands num den) + 1))

omit [DecidableEq α] in
theorem widthPolynomial_eval (num den : Expr α) (width : Nat) :
    (widthPolynomial num den).eval width = staticWidth (commands num den) width := by
  simp only [widthPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, staticWidth, Nat.add_assoc]

def timePolynomial (num den : Expr α) : Polynomial Nat :=
  runtimePolynomial (commands num den) +
    (runtimePolynomial (clearCommands num den)).comp (widthPolynomial num den) +
    2 * widthPolynomial num den + 5

omit [DecidableEq α] in
theorem timePolynomial_eval (num den : Expr α) (width : Nat) :
    (timePolynomial num den).eval width =
      (runtimePolynomial (commands num den)).eval width +
        (runtimePolynomial (clearCommands num den)).eval (staticWidth (commands num den) width) +
        2 * staticWidth (commands num den) width + 5 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_comp, widthPolynomial_eval]

theorem consumed_width (num den : Expr α) (values : Reg num den → Nat) (width : Nat)
    (h : ∀ r, (values r).size ≤ width) :
    ∀ r, (consumed num den values r).size ≤ width := by
  intro r
  by_cases hd : r = denRoot num den
  · subst r; simp [consumed]
  · by_cases hn : r = numRoot num den
    · subst r; simp [consumed, hd]
    · simpa [consumed, hd, hn] using h r

theorem exec (num den : Expr α) (slot : (Reg num den ⊕ Fin 6) ↪ K)
    (output : K) (outside : ∀ i, slot i ≠ output) (base : K → List Bool)
    (values : α → Nat) (ambient : A) (width : Nat)
    (hwidth : ∀ a, (values a).size ≤ width) :
    ∃ steps ≤ (timePolynomial num den).eval width,
      Exec (code num den slot output)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (initial num den values)⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot (outputTapes output base (record num den values))
            (initial num den values)⟩ := by
  classical
  let start := initial num den values
  let computed := resultOf (commands num den) start
  let afterNum := Function.update computed (numRoot num den) 0
  let afterBoth := consumed num den computed
  let marked := Function.update base output (true :: base output)
  let writtenNum := Function.update marked output
    ((BinaryEncoding.natBits (computed (numRoot num den))).reverse ++ marked output)
  let writtenBoth := Function.update writtenNum output
    ((BinaryEncoding.natBits (afterNum (denRoot num den))).reverse ++ writtenNum output)
  let w := staticWidth (commands num den) width
  have hw0 : ∀ r, (start r).size ≤ width := initial_width num den values width hwidth
  have hw : ∀ r, (computed r).size ≤ w :=
    BinaryRegisterStructured.final_width (commands num den) start width hw0
  obtain ⟨calcSteps, calcBound, calcRun⟩ :=
    BinaryRegisterStructured.exec_polynomial slot (commands num den) base start
      (ready num den values) ambient width hw0
  have outside' : ¬ ∃ i, slot i = output := by rintro ⟨i, hi⟩; exact outside i hi
  have markerRun : Exec (.atom (.push output (fun _ => true) .done))
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base computed⟩ 1
      ⟨BinaryAddMachine.clean ambient, registerTapes slot marked computed⟩ := by
    rw [RegisterFrameEmission.external_update slot base computed output outside]
    simpa only [Action.eval, registerTapes_other slot base computed output outside', marked] using
      Exec.atom (.push output (fun _ => true) .done)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base computed⟩
  have numRun := RegisterFrameEmission.exec slot marked computed
    (numRoot num den) output outside ambient
  have denRun := RegisterFrameEmission.exec slot writtenNum afterNum
    (denRoot num den) output outside ambient
  change Exec (RegisterFrameEmission.code (slot (.inl (numRoot num den))) output)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot marked computed⟩
    ((computed (numRoot num den)).size + 1)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot writtenNum afterNum⟩ at numRun
  change Exec (RegisterFrameEmission.code (slot (.inl (denRoot num den))) output)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot writtenNum afterNum⟩
    ((afterNum (denRoot num den)).size + 1)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot writtenBoth afterBoth⟩ at denRun
  have hwc : ∀ r, (afterBoth r).size ≤ w := consumed_width num den computed w hw
  obtain ⟨clearSteps, clearBound, clearRun⟩ :=
    BinaryRegisterStructured.exec_polynomial slot (clearCommands num den) writtenBoth afterBoth
      (clear_ready num den afterBoth) ambient w hwc
  have denStill : afterNum (denRoot num den) = computed (denRoot num den) := by
    simp [afterNum, Ne.symm (numRoot_ne_denRoot num den)]
  have numValue : computed (numRoot num den) = eval values num := numerator_output num den values
  have denValue : computed (denRoot num den) = eval values den := denominator_output num den values
  have clearValue : resultOf (clearCommands num den) afterBoth = start :=
    clear_after_consumed num den values
  have writtenValue : writtenBoth = outputTapes output base (record num den values) := by
    simp only [writtenBoth, denStill, numValue, denValue, writtenNum, marked,
      Function.update_self, Function.update_idem, outputTapes, record,
      List.reverse_cons, List.reverse_append, List.append_assoc, List.singleton_append]
  let total := calcSteps + (1 + ((computed (numRoot num den)).size + 1 +
    ((afterNum (denRoot num den)).size + 1 + clearSteps)))
  refine ⟨total, ?_, ?_⟩
  · have hn := hw (numRoot num den)
    have hd := hw (denRoot num den)
    rw [timePolynomial_eval]
    change total ≤ (runtimePolynomial (commands num den)).eval width +
      (runtimePolynomial (clearCommands num den)).eval w + 2 * w + 5
    dsimp [total]
    rw [denStill]
    omega
  · rw [clearValue] at clearRun
    have combined := Exec.seq calcRun (Exec.seq markerRun
      (Exec.seq numRun (Exec.seq denRun clearRun)))
    rw [writtenValue] at combined
    exact combined

theorem exec_item (D : InventoryData) (i : D.Item)
    (slot : (Reg
      (PackingItemExpression.numerator (D.itemSubclass i) (PackingItemExpression.itemCoordinate D i))
      PackingItemExpression.denominator ⊕ Fin 6) ↪ K)
    (output : K) (outside : ∀ j, slot j ≠ output) (base : K → List Bool)
    (ambient : A) (width : Nat)
    (hwidth : ∀ a, (PackingItemExpression.values D i a).size ≤ width) :
    let num := PackingItemExpression.numerator (D.itemSubclass i) (PackingItemExpression.itemCoordinate D i)
    let den := PackingItemExpression.denominator
    ∃ steps ≤ (timePolynomial num den).eval width,
      Exec (code num den slot output)
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot base (initial num den (PackingItemExpression.values D i))⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot (outputTapes output base
            (true :: (BinaryEncoding.natBits (D.itemRawPair i).1 ++
              BinaryEncoding.natBits (D.itemRawPair i).2)))
            (initial num den (PackingItemExpression.values D i))⟩ := by
  simpa only [record, PackingItemExpression.eval_item_numerator,
    PackingItemExpression.eval_item_denominator] using
    exec (PackingItemExpression.numerator (D.itemSubclass i) (PackingItemExpression.itemCoordinate D i))
      PackingItemExpression.denominator slot output outside base
      (PackingItemExpression.values D i) ambient width hwidth

end BinPackingGap.PackingItemBlockMachine

namespace BinPackingGap.PackingChunkMachine

open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler
open PairExpressionCompiler
open PackingItemBlockMachine (outputTapes)

variable {α δ K A : Type} [DecidableEq α] [DecidableEq K]

def code (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K) (output : K) :
    List δ → Code (K := K) (S := BinaryAddMachine.State A)
  | [] => .atom .done
  | [d] => PackingItemBlockMachine.code (numerator d) denominator (slot d) output
  | d :: e :: rest =>
      .seq (PackingItemBlockMachine.code (numerator d) denominator (slot d) output)
        (code numerator denominator slot output (e :: rest))

def records (numerator : δ → Expr α) (denominator : Expr α)
    (values : δ → α → Nat) (descriptors : List δ) : List Bool :=
  descriptors.flatMap (fun d => PackingItemBlockMachine.record
    (numerator d) denominator (values d))

omit [DecidableEq α] in
@[simp] theorem records_nil (numerator : δ → Expr α) (denominator : Expr α)
    (values : δ → α → Nat) : records numerator denominator values [] = [] := rfl

omit [DecidableEq α] in
@[simp] theorem records_cons (numerator : δ → Expr α) (denominator : Expr α)
    (values : δ → α → Nat) (d : δ) (rest : List δ) :
    records numerator denominator values (d :: rest) =
      PackingItemBlockMachine.record (numerator d) denominator (values d) ++
        records numerator denominator values rest := by
  simp only [records, List.flatMap_cons]

def timePolynomial (numerator : δ → Expr α) (denominator : Expr α) :
    List δ → Polynomial Nat
  | [] => 1
  | [d] => PackingItemBlockMachine.timePolynomial (numerator d) denominator
  | d :: e :: rest => PackingItemBlockMachine.timePolynomial (numerator d) denominator +
      timePolynomial numerator denominator (e :: rest)

omit [DecidableEq α] in
theorem timePolynomial_eq_sum (numerator : δ → Expr α) (denominator : Expr α)
    (descriptors : List δ) (nonempty : descriptors ≠ []) :
    timePolynomial numerator denominator descriptors =
      (descriptors.map (fun d => PackingItemBlockMachine.timePolynomial
        (numerator d) denominator)).sum := by
  cases descriptors with
  | nil => exact (nonempty rfl).elim
  | cons d rest =>
      clear nonempty
      induction rest generalizing d with
      | nil => simp [timePolynomial]
      | cons e rest ih =>
          rw [timePolynomial, ih]
          simp only [List.map_cons, List.sum_cons]

@[simp] theorem outputTapes_nil (output : K) (base : K → List Bool) :
    outputTapes output base [] = base := by
  simp [outputTapes]

theorem outputTapes_append (output : K) (base : K → List Bool) (first second : List Bool) :
    outputTapes output (outputTapes output base first) second =
      outputTapes output base (first ++ second) := by
  simp only [outputTapes, Function.update_self, Function.update_idem,
    List.reverse_append, List.append_assoc]

theorem shape_after_output {R : Type} (slot : (R ⊕ Fin 6) ↪ K)
    (output : K) (outside : ∀ i, slot i ≠ output) (base : K → List Bool)
    (values : R → Nat) (shape : registerTapes slot base values = base) (word : List Bool) :
    registerTapes slot (outputTapes output base word) values =
      outputTapes output base word := by
  classical
  unfold outputTapes
  rw [RegisterFrameEmission.external_update slot base values output outside, shape]

private theorem exec_one (num den : Expr α) (slot : (Reg num den ⊕ Fin 6) ↪ K)
    (output : K) (outside : ∀ i, slot i ≠ output) (base : K → List Bool)
    (values : α → Nat) (ambient : A) (width : Nat)
    (shape : registerTapes slot base (initial num den values) = base)
    (hwidth : ∀ a, (values a).size ≤ width) :
    ∃ steps ≤ (PackingItemBlockMachine.timePolynomial num den).eval width,
      Exec (PackingItemBlockMachine.code num den slot output)
        ⟨BinaryAddMachine.clean ambient, base⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          outputTapes output base (PackingItemBlockMachine.record num den values)⟩ := by
  obtain ⟨steps, bound, run⟩ :=
    PackingItemBlockMachine.exec num den slot output outside base values ambient width hwidth
  refine ⟨steps, bound, ?_⟩
  rw [shape, shape_after_output slot output outside base _ shape] at run
  exact run

theorem exec (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K)
    (output : K) (outside : ∀ d i, slot d i ≠ output)
    (descriptors : List δ) (base : K → List Bool) (values : δ → α → Nat)
    (ambient : A) (width : Nat)
    (shape : ∀ d ∈ descriptors,
      registerTapes (slot d) base (initial (numerator d) denominator (values d)) = base)
    (hwidth : ∀ d ∈ descriptors, ∀ a, (values d a).size ≤ width) :
    ∃ steps ≤ (timePolynomial numerator denominator descriptors).eval width,
      Exec (code numerator denominator slot output descriptors)
        ⟨BinaryAddMachine.clean ambient, base⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          outputTapes output base (records numerator denominator values descriptors)⟩ := by
  induction descriptors generalizing base with
  | nil =>
      refine ⟨1, ?_, ?_⟩
      · simp [timePolynomial]
      · simpa only [code, records_nil, outputTapes_nil, Action.eval] using
          Exec.atom (.done : Action K (BinaryAddMachine.State A))
            ⟨BinaryAddMachine.clean ambient, base⟩
  | cons d rest ih =>
      have headShape := shape d (by simp)
      have headWidth := hwidth d (by simp)
      obtain ⟨headSteps, headBound, headRun⟩ :=
        exec_one (numerator d) denominator (slot d) output (outside d)
          base (values d) ambient width headShape headWidth
      cases rest with
      | nil =>
          refine ⟨headSteps, headBound, ?_⟩
          simpa only [code, records_cons, records_nil, List.append_nil] using headRun
      | cons e rest =>
          let middle := outputTapes output base
            (PackingItemBlockMachine.record (numerator d) denominator (values d))
          have tailShape : ∀ x ∈ e :: rest,
              registerTapes (slot x) middle
                (initial (numerator x) denominator (values x)) = middle := by
            intro x hx
            exact shape_after_output (slot x) output (outside x) base _
              (shape x (List.mem_cons.mpr (Or.inr hx))) _
          have tailWidth : ∀ x ∈ e :: rest, ∀ a, (values x a).size ≤ width := by
            intro x hx
            exact hwidth x (List.mem_cons.mpr (Or.inr hx))
          obtain ⟨tailSteps, tailBound, tailRun⟩ := ih middle tailShape tailWidth
          refine ⟨headSteps + tailSteps, ?_, ?_⟩
          · change headSteps + tailSteps ≤
              (PackingItemBlockMachine.timePolynomial (numerator d) denominator +
                timePolynomial numerator denominator (e :: rest)).eval width
            rw [Polynomial.eval_add]
            exact Nat.add_le_add headBound tailBound
          · have combined := Exec.seq headRun tailRun
            simpa only [code, middle, outputTapes_append, records_cons] using combined

@[simp] theorem final_output (output : K) (base : K → List Bool) (word : List Bool) :
    outputTapes output base word output = word.reverse ++ base output := by
  simp [outputTapes]

theorem final_frame (output : K) (base : K → List Bool) (word : List Bool)
    (tape : K) (different : tape ≠ output) :
    outputTapes output base word tape = base tape := by
  simp [outputTapes, different]

end BinPackingGap.PackingChunkMachine

namespace BinPackingGap.PackingDescriptorExpression

open NatExpressionCompiler PackingInventoryDescriptors

def instantiate (fixed : InventoryData) (graph : GraphInput) (R k : Nat) : InventoryData :=
  { fixed with graph := graph, R := R, k := k }

@[simp] theorem vertexDescriptors_instantiate (fixed : InventoryData)
    (graph : GraphInput) (R k : Nat) :
    vertexDescriptors (instantiate fixed graph R k) = vertexDescriptors fixed := by
  have htree : (instantiate fixed graph R k).treeRowList = fixed.treeRowList := by
    rfl
  have hpositive : (instantiate fixed graph R k).positiveLocalList =
      fixed.positiveLocalList := by
    unfold InventoryData.positiveLocalList
    apply congrArg Finset.toList
    ext r
    constructor <;> intro _ <;> exact Finset.mem_univ _
  have hsubclass : (instantiate fixed graph R k).treeSubclass = fixed.treeSubclass := by
    funext r
    rcases r with p | (m | pad) <;> rfl
  have htreeDescriptor :
      PackingCoordinateExpression.treeDescriptor (instantiate fixed graph R k) =
        PackingCoordinateExpression.treeDescriptor fixed := by
    funext r
    rcases r with ⟨node, copy⟩ | (⟨node, copy⟩ | copy) <;> rfl
  have hlocal : positiveDescriptor (instantiate fixed graph R k) =
      positiveDescriptor fixed := by
    funext r
    apply Prod.ext rfl
    apply congrArg PackingCoordinateExpression.Descriptor.localDepth
    apply Fin.ext
    rfl
  simp only [vertexDescriptors, htree, hpositive, hsubclass, htreeDescriptor, hlocal]
  rfl

@[simp] theorem jobDescriptors_instantiate (fixed : InventoryData)
    (graph : GraphInput) (R k : Nat) :
    jobDescriptors (instantiate fixed graph R k) = jobDescriptors fixed := rfl

def numerator (D : InventoryData) (descriptor : ItemDescriptor D) :
    Expr PackingItemExpression.Variable :=
  PackingItemExpression.numerator descriptor.1
    (PackingCoordinateExpression.expression D.geometryBound descriptor.2)

@[simp] theorem numerator_instantiate (fixed : InventoryData)
    (graph : GraphInput) (R k : Nat) (descriptor : ItemDescriptor fixed) :
    numerator (instantiate fixed graph R k) descriptor = numerator fixed descriptor := rfl

def values (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat) :
    PackingItemExpression.Variable → Nat
  | .vertexPower => 3 ^ D.graph.n
  | .geometry => D.coordinateDenominator
  | .labelPower => NaturalPackingNumerator.labelPower label
  | .totalPower => (D.R + 1) ^ D.graph.edges.length
  | .edgePower => (D.R + 1) ^ edge
  | .repetitionOne => rep

theorem coordinate_values (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat) :
    values D label edge rep ∘ PackingItemExpression.coordinateVariable =
      PackingCoordinateExpression.registers D edge rep := by
  funext v
  cases v <;> rfl

theorem replacement_values (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat)
    (descriptor : ItemDescriptor D) :
    (fun v => eval (values D label edge rep)
      (PackingItemExpression.scalarReplacement
        (PackingCoordinateExpression.expression D.geometryBound descriptor.2) v)) =
      PackingScalarExpression.values D.coordinateDenominator label
        ((PackingCoordinateExpression.expression D.geometryBound descriptor.2).eval
          (PackingCoordinateExpression.registers D edge rep)) := by
  funext v
  cases v with
  | vertexPower => rfl
  | geometry => rfl
  | labelPower => rfl
  | coordinatePositive =>
      simp only [PackingItemExpression.scalarReplacement, eval_rename, coordinate_values]
      rfl
  | coordinateNegative =>
      simp only [PackingItemExpression.scalarReplacement, eval_rename, coordinate_values]
      rfl

theorem eval_numerator (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat)
    (descriptor : ItemDescriptor D) :
    eval (values D label edge rep) (numerator D descriptor) =
      (rawOfDescriptor D label edge rep descriptor).1 := by
  rw [numerator, PackingItemExpression.numerator, eval_substitute, replacement_values,
    PackingScalarExpression.eval_numerator]
  rfl

theorem eval_denominator (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat) :
    eval (values D label edge rep) PackingItemExpression.denominator =
      IntegerPackingArithmetic.sizeDenominator D.graph.n D.coordinateDenominator := rfl

def rawRecord (pair : Nat × Nat) : List Bool :=
  true :: (BinaryEncoding.natBits pair.1 ++ BinaryEncoding.natBits pair.2)

def rawRecords (items : RawInstance) : List Bool := items.flatMap rawRecord

theorem record_eq (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat)
    (descriptor : ItemDescriptor D) :
    PackingItemBlockMachine.record (numerator D descriptor) PackingItemExpression.denominator
      (values D label edge rep) = rawRecord (rawOfDescriptor D label edge rep descriptor) := by
  simp only [PackingItemBlockMachine.record, eval_numerator, eval_denominator,
    rawRecord, rawOfDescriptor]

theorem chunk_records (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat)
    (descriptors : List (ItemDescriptor D)) :
    PackingChunkMachine.records (numerator D) PackingItemExpression.denominator
      (fun _ => values D label edge rep) descriptors =
      rawRecords (descriptors.map (rawOfDescriptor D label edge rep)) := by
  simp only [PackingChunkMachine.records, rawRecords, List.flatMap_map, record_eq]

theorem rawInstanceBits_eq (items : RawInstance) :
    BinaryEncoding.rawInstanceBits items = rawRecords items ++ [false] := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
        BinaryEncoding.pairBits, rawRecords, List.flatMap_cons, rawRecord] at *
      rw [ih]
      simp only [List.cons_append, List.append_assoc]

theorem reductionOutputBits_eq (B : Nat) (items : RawInstance) :
    BinaryEncoding.rawReductionOutputBits (B, items) =
      BinaryEncoding.natBits B ++ rawRecords items ++ [false] := by
  rw [BinaryEncoding.rawReductionOutputBits, rawInstanceBits_eq, List.append_assoc]

end BinPackingGap.PackingDescriptorExpression

namespace BinPackingGap.PackingVertexLoop

open NatExpressionCompiler

variable {α δ : Type} [DecidableEq α]

def vertexInput (input : α → Nat) (power : α) (v : Nat) : α → Nat :=
  Function.update input power (3 ^ (v + 1))

@[simp] theorem vertexInput_power (input : α → Nat) (power : α) (v : Nat) :
    vertexInput input power v power = 3 ^ (v + 1) := by
  simp [vertexInput]

theorem vertexInput_other (input : α → Nat) (power : α) (v : Nat)
    (a : α) (different : a ≠ power) : vertexInput input power v a = input a := by
  simp [vertexInput, different]

theorem vertexInput_update (input : α → Nat) (power : α) (v : Nat) :
    Function.update (vertexInput input power v) power
      (3 * vertexInput input power v power) = vertexInput input power (v + 1) := by
  have powerStep : 3 * 3 ^ (v + 1) = 3 ^ ((v + 1) + 1) :=
    (Nat.mul_comm 3 (3 ^ (v + 1))).trans (Nat.pow_succ 3 (v + 1)).symm
  rw [vertexInput_power]
  unfold vertexInput
  rw [Function.update_idem, powerStep]

theorem pow3_size_le (n : Nat) : (3 ^ n).size ≤ 2 * n + 1 := by
  have bound := BinaryArithmetic.size_pow_le 3 n
  have sizeThree : (3 : Nat).size = 2 := by decide
  rw [sizeThree, Nat.mul_comm n 2] at bound
  exact bound

def aggregateWidth (inputWidth start count : Nat) : Nat :=
  inputWidth + 2 * (start + count + 1) + 1

theorem vertexInput_size_le (input : α → Nat) (power : α)
    (inputWidth start count v : Nat)
    (initial : ∀ a, (input a).size ≤ inputWidth) (hv : v ≤ start + count) :
    ∀ a, (vertexInput input power v a).size ≤ aggregateWidth inputWidth start count := by
  intro a
  by_cases same : a = power
  · subst a
    rw [vertexInput_power]
    have bound := pow3_size_le (v + 1)
    unfold aggregateWidth
    omega
  · rw [vertexInput_other input power v a same]
    have bound := initial a
    unfold aggregateWidth
    omega

def stream (numerator : δ → Expr α) (denominator : Expr α) (descriptors : List δ)
    (input : α → Nat) (power : α) (start : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 =>
      PackingChunkMachine.records numerator denominator
        (fun _ => vertexInput input power start) descriptors ++
      stream numerator denominator descriptors input power (start + 1) count

@[simp] theorem stream_zero (numerator : δ → Expr α) (denominator : Expr α)
    (descriptors : List δ) (input : α → Nat) (power : α) (start : Nat) :
    stream numerator denominator descriptors input power start 0 = [] := rfl

@[simp] theorem stream_succ (numerator : δ → Expr α) (denominator : Expr α)
    (descriptors : List δ) (input : α → Nat) (power : α) (start count : Nat) :
    stream numerator denominator descriptors input power start (count + 1) =
      PackingChunkMachine.records numerator denominator
        (fun _ => vertexInput input power start) descriptors ++
      stream numerator denominator descriptors input power (start + 1) count := rfl

end BinPackingGap.PackingVertexLoop

namespace BinPackingGap.PackingJobBody

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

def nextInput (input : α → Nat) (power repetition : α) (rightValue : Nat) : α → Nat :=
  Function.update (Function.update input power rightValue) repetition (input repetition + 1)

@[simp] theorem nextInput_repetition (input : α → Nat) (power repetition : α)
    (rightValue : Nat) :
    nextInput input power repetition rightValue repetition = input repetition + 1 := by
  simp [nextInput]

@[simp] theorem nextInput_power (input : α → Nat) (power repetition : α)
    (different : power ≠ repetition) (rightValue : Nat) :
    nextInput input power repetition rightValue power = rightValue := by
  simp [nextInput, different]

def pairRecords (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (input : α → Nat) (power : α) (leftValue rightValue : Nat) : List Bool :=
  PackingChunkMachine.records num den
      (fun _ => Function.update input power leftValue) descriptors ++
    PackingChunkMachine.records num den
      (fun _ => Function.update input power rightValue) descriptors

def body (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (leftPower rightPower one temp : Other)
    (different : one ≠ temp) (output : Extra) :
    Code (K := Tape num den Other Extra) (S := State) :=
  .seq (PackingLayoutCommands.inputFromOther num den power leftPower)
    (.seq (PackingArithmeticProgram.code
      (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors))
      (.seq (PackingLayoutCommands.inputFromOther num den power rightPower)
        (.seq (PackingArithmeticProgram.code
          (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors))
          (PackingRegisterUpdate.code
            (PackingVertexUpdate.updateSlots num den repetition one temp different) .add))))

def bodyTimePolynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (leftPower rightPower : Other) : Polynomial Nat :=
  PackingLayoutCommands.inputFromOtherTime num den power leftPower +
    PackingLayoutCommands.inputFromOtherTime num den power rightPower +
    2 * (PackingChunkMachine.timePolynomial num den descriptors + 1) +
    64 * (Polynomial.X + 2) ^ 2

omit [DecidableEq α] [DecidableEq δ] [DecidableEq Other] in
theorem bodyTimePolynomial_eval (num : δ → Expr α) (den : Expr α)
    (descriptors : List δ) (power : α) (leftPower rightPower : Other) (width : Nat) :
    (bodyTimePolynomial num den descriptors power leftPower rightPower).eval width =
      (PackingLayoutCommands.inputFromOtherTime num den power leftPower).eval width +
        (PackingLayoutCommands.inputFromOtherTime num den power rightPower).eval width +
        2 * ((PackingChunkMachine.timePolynomial num den descriptors).eval width + 1) +
        64 * (width + 2) ^ 2 := by
  simp [bodyTimePolynomial]

private theorem update_size_le (input : α → Nat) (power : α) (value width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (hv : value.size ≤ width) :
    ∀ a, (Function.update input power value a).size ≤ width := by
  intro a
  by_cases ha : a = power
  · subst a
    simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne ha] using hi a

private theorem layout_external_update (num : δ → Expr α) (den : Expr α)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (external : Extra) (word : List Bool) :
    tapes num den (Function.update base (.inr external) word) input other =
      Function.update (tapes num den base input other) (.inr external) word := by
  apply RegisterFrameEmission.external_update
  intro i
  simp [registers]

private theorem layout_output (num : δ → Expr α) (den : Expr α)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (output : Extra) (word : List Bool) :
    outputTapes (.inr output) (tapes num den base input other) word =
      tapes num den (outputTapes (.inr output) base word) input other := by
  unfold outputTapes
  rw [tapes_extra, layout_external_update]

private theorem chunk_exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (output : Extra) (base : Tape num den Other Extra → List Bool)
    (input : α → Nat) (other : Other → Nat) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (state : State) :
    ∃ steps ≤ (PackingChunkMachine.timePolynomial num den descriptors).eval width + 1,
      Exec (PackingArithmeticProgram.code
          (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors))
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den (outputTapes (.inr output) base
            (PackingChunkMachine.records num den (fun _ => input) descriptors)) input other⟩ := by
  have chunk := PackingChunkMachine.exec num den (itemSlots num den) (.inr output)
    (fun d => itemSlots_outside num den d output) descriptors
    (tapes num den base input other) (fun _ => input) () width
    (fun d _ => item_shape num den base input other d) (fun _ _ => hi)
  obtain ⟨steps, bound, run⟩ := PackingArithmeticProgram.exec_in_time
    (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors)
    _ _ _ state chunk
  rw [layout_output] at run
  exact ⟨steps, bound, run⟩

theorem body_exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (inputDifferent : power ≠ repetition)
    (leftPower rightPower one temp : Other) (different : one ≠ temp) (output : Extra)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat) (other : Other → Nat)
    (hone : other one = 1) (htemp : other temp = 0) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width)
    (state : State) :
    ∃ steps ≤ (bodyTimePolynomial num den descriptors power leftPower rightPower).eval width,
      Exec (body num den descriptors power repetition leftPower rightPower one temp different output)
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den
            (outputTapes (.inr output) base
              (pairRecords num den descriptors input power (other leftPower) (other rightPower)))
            (nextInput input power repetition (other rightPower)) other⟩ := by
  let leftInput := Function.update input power (other leftPower)
  let rightInput := Function.update input power (other rightPower)
  let leftWord := PackingChunkMachine.records num den (fun _ => leftInput) descriptors
  let rightWord := PackingChunkMachine.records num den (fun _ => rightInput) descriptors
  have leftWidth : ∀ a, (leftInput a).size ≤ width :=
    update_size_le input power (other leftPower) width hi (ho leftPower)
  have rightWidth : ∀ a, (rightInput a).size ≤ width :=
    update_size_le input power (other rightPower) width hi (ho rightPower)
  obtain ⟨copyLeftSteps, copyLeftBound, copyLeftRun⟩ :=
    PackingLayoutCommands.inputFromOther_exec num den power leftPower base input other
      state width hi ho
  obtain ⟨emitLeftSteps, emitLeftBound, emitLeftRun⟩ :=
    chunk_exec num den descriptors output base leftInput other width leftWidth
      (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨copyRightSteps, copyRightBound, copyRightRun⟩ :=
    PackingLayoutCommands.inputFromOther_exec num den power rightPower
      (outputTapes (.inr output) base leftWord) leftInput other
      (.arithmetic (BinaryAddMachine.clean ())) width leftWidth ho
  simp only [leftInput, Function.update_idem] at copyRightRun
  obtain ⟨emitRightSteps, emitRightBound, emitRightRun⟩ :=
    chunk_exec num den descriptors output (outputTapes (.inr output) base leftWord)
      rightInput other width rightWidth (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨updateSteps, updateBound, updateRun⟩ :=
    PackingVertexUpdate.general_exec num den repetition one temp different .add
      (outputTapes (.inr output) (outputTapes (.inr output) base leftWord) rightWord)
      rightInput other htemp (.arithmetic (BinaryAddMachine.clean ()))
  have next : Function.update rightInput repetition
      (PackingRegisterUpdate.operation .add (other one) (rightInput repetition)) =
      nextInput input power repetition (other rightPower) := by
    simp only [rightInput, PackingRegisterUpdate.operation, hone,
      Function.update_of_ne (Ne.symm inputDifferent), nextInput]
    exact congrArg
      (Function.update (Function.update input power (other rightPower)) repetition)
      (Nat.add_comm 1 (input repetition))
  rw [next] at updateRun
  refine ⟨copyLeftSteps + (emitLeftSteps + (copyRightSteps + (emitRightSteps + updateSteps))),
    ?_, ?_⟩
  · rw [bodyTimePolynomial_eval]
    have sizeOne : (1 : Nat).size = 1 := by decide
    rw [hone, sizeOne] at updateBound
    have hr := rightWidth repetition
    have square : (1 + (rightInput repetition).size + 1) ^ 2 ≤ (width + 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) _
    have ub := updateBound.trans (Nat.mul_le_mul_left 64 square)
    omega
  · have combined := Exec.seq copyLeftRun
      (Exec.seq emitLeftRun (Exec.seq copyRightRun (Exec.seq emitRightRun updateRun)))
    simpa only [body, leftInput, rightInput, leftWord, rightWord, pairRecords,
      PackingChunkMachine.outputTapes_append] using combined

end BinPackingGap.PackingJobBody

namespace BinPackingGap.PackingVertexRecords

open NatExpressionCompiler

private theorem finRange_cons (n : Nat) :
    List.finRange (n + 1) = (0 : Fin (n + 1)) :: (List.finRange n).map Fin.succ := by
  rw [← List.ofFn_id, List.ofFn_succ, List.ofFn_eq_map]
  rfl

theorem stream_eq_finRange {α δ : Type} [DecidableEq α]
    (numerator : δ → Expr α) (denominator : Expr α) (descriptors : List δ)
    (input : α → Nat) (power : α) (start count : Nat) :
    PackingVertexLoop.stream numerator denominator descriptors input power start count =
      (List.finRange count).flatMap (fun i =>
        PackingChunkMachine.records numerator denominator
          (fun _ => PackingVertexLoop.vertexInput input power (start + i.val)) descriptors) := by
  induction count generalizing start with
  | zero => simp [PackingVertexLoop.stream]
  | succ count ih =>
      simp only [PackingVertexLoop.stream_succ, finRange_cons, List.flatMap_cons,
        List.flatMap_map, Fin.val_zero, Fin.val_succ, Nat.add_zero, ih]
      congr 1
      apply List.flatMap_congr
      intro i _
      have index : start + 1 + i.val = start + (i.val + 1) := by omega
      rw [index]

theorem values_vertexInput (D : InventoryData) (v : D.Vertex) :
    PackingVertexLoop.vertexInput (PackingDescriptorExpression.values D none 0 0)
        .labelPower v.val =
      PackingDescriptorExpression.values D (some v) 0 0 := by
  funext coordinate
  cases coordinate <;>
    simp [PackingVertexLoop.vertexInput, PackingDescriptorExpression.values,
      NaturalPackingNumerator.labelPower]

theorem rawRecords_flatMap {ι : Type} (indices : List ι) (items : ι → RawInstance) :
    PackingDescriptorExpression.rawRecords (indices.flatMap items) =
      indices.flatMap (fun i => PackingDescriptorExpression.rawRecords (items i)) := by
  simp only [PackingDescriptorExpression.rawRecords, List.flatMap_assoc]

theorem stream_eq_vertexStream (D : InventoryData) :
    PackingVertexLoop.stream (PackingDescriptorExpression.numerator D)
        PackingItemExpression.denominator (PackingInventoryDescriptors.vertexDescriptors D)
        (PackingDescriptorExpression.values D none 0 0) .labelPower 0 D.graph.n =
      PackingDescriptorExpression.rawRecords (PackingInventoryDescriptors.vertexStream D) := by
  rw [stream_eq_finRange, PackingInventoryDescriptors.vertexStream, rawRecords_flatMap]
  apply List.flatMap_congr
  intro v _
  simpa only [Nat.zero_add, values_vertexInput] using
    PackingDescriptorExpression.chunk_records D (some v) 0 0
      (PackingInventoryDescriptors.vertexDescriptors D)

end BinPackingGap.PackingVertexRecords

namespace BinPackingGap.PackingJobLoop

section

open NatExpressionCompiler

variable {α δ : Type} [DecidableEq α]

def iterationInput (input : α → Nat) (power repetition : α) (right : Nat) :
    Nat → α → Nat
  | 0 => input
  | n + 1 => Function.update (Function.update input power right) repetition
      (input repetition + (n + 1))

@[simp] theorem iterationInput_zero (input : α → Nat) (power repetition : α) (right : Nat) :
    iterationInput input power repetition right 0 = input := rfl

@[simp] theorem iterationInput_rep (input : α → Nat) (power repetition : α)
    (right n : Nat) :
    iterationInput input power repetition right n repetition = input repetition + n := by
  cases n <;> simp [iterationInput]

theorem iterationInput_power (input : α → Nat) (power repetition : α) (right : Nat)
    (distinct : power ≠ repetition) (n : Nat) (positive : 0 < n) :
    iterationInput input power repetition right n power = right := by
  cases n with
  | zero => omega
  | succ n => simp [iterationInput, distinct]

theorem iterationInput_other (input : α → Nat) (power repetition : α)
    (right n : Nat) (a : α) (notPower : a ≠ power) (notRepetition : a ≠ repetition) :
    iterationInput input power repetition right n a = input a := by
  cases n <;> simp [iterationInput, notPower, notRepetition]

theorem iterationInput_succ (input : α → Nat) (power repetition : α) (right : Nat)
    (distinct : power ≠ repetition) (n : Nat) :
    iterationInput (PackingJobBody.nextInput input power repetition right)
        power repetition right n =
      iterationInput input power repetition right (n + 1) := by
  cases n with
  | zero => rfl
  | succ n =>
      funext a
      by_cases atRepetition : a = repetition
      · subst a
        simp [iterationInput, PackingJobBody.nextInput,
          Nat.add_comm, Nat.add_left_comm]
      · by_cases atPower : a = power
        · subst a
          simp [iterationInput, PackingJobBody.nextInput, distinct]
        · simp [iterationInput, PackingJobBody.nextInput, atRepetition, atPower]

theorem nextInput_iterationInput (input : α → Nat) (power repetition : α) (right : Nat)
    (distinct : power ≠ repetition) (n : Nat) :
    PackingJobBody.nextInput (iterationInput input power repetition right n)
        power repetition right =
      iterationInput input power repetition right (n + 1) := by
  cases n with
  | zero => rfl
  | succ n =>
      funext a
      by_cases atRepetition : a = repetition
      · subst a
        simp [iterationInput, PackingJobBody.nextInput, Nat.add_assoc]
      · by_cases atPower : a = power
        · subst a
          simp [iterationInput, PackingJobBody.nextInput, distinct]
        · simp [iterationInput, PackingJobBody.nextInput, atRepetition, atPower]

def aggregateWidth (inputWidth otherWidth count : Nat) : Nat :=
  inputWidth + otherWidth + count + 2

private theorem size_le_succ (n : Nat) : n.size ≤ n + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have bound := BinaryArithmetic.size_add_le n 1
      have sizeOne : (1 : Nat).size = 1 := by decide
      rw [sizeOne] at bound
      omega

theorem iterationInput_size_le (input : α → Nat) (power repetition : α) (right : Nat)
    (distinct : power ≠ repetition) (inputWidth otherWidth count n : Nat)
    (within : n ≤ count) (initial : ∀ a, (input a).size ≤ inputWidth)
    (rightBound : right.size ≤ otherWidth) :
    ∀ a, (iterationInput input power repetition right n a).size ≤
      aggregateWidth inputWidth otherWidth count := by
  intro a
  by_cases atRepetition : a = repetition
  · subst a
    rw [iterationInput_rep]
    have bound := BinaryArithmetic.size_add_le (input repetition) n
    have sizeN := size_le_succ n
    have sizeInitial := initial repetition
    unfold aggregateWidth
    omega
  · cases n with
    | zero =>
        simp only [iterationInput_zero]
        have bound := initial a
        unfold aggregateWidth
        omega
    | succ n =>
        by_cases atPower : a = power
        · subst a
          rw [iterationInput_power input power repetition right distinct (n + 1)
            (Nat.succ_pos n)]
          unfold aggregateWidth
          omega
        · rw [iterationInput_other input power repetition right (n + 1) a
            atPower atRepetition]
          have bound := initial a
          unfold aggregateWidth
          omega

def stream (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (input : α → Nat) (power repetition : α) (left right : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => PackingJobBody.pairRecords num den descriptors input power left right ++
      stream num den descriptors (PackingJobBody.nextInput input power repetition right)
        power repetition left right n

@[simp] theorem stream_zero (num : δ → Expr α) (den : Expr α)
    (descriptors : List δ) (input : α → Nat) (power repetition : α) (left right : Nat) :
    stream num den descriptors input power repetition left right 0 = [] := rfl

@[simp] theorem stream_succ (num : δ → Expr α) (den : Expr α)
    (descriptors : List δ) (input : α → Nat) (power repetition : α) (left right n : Nat) :
    stream num den descriptors input power repetition left right (n + 1) =
      PackingJobBody.pairRecords num den descriptors input power left right ++
        stream num den descriptors (PackingJobBody.nextInput input power repetition right)
          power repetition left right n := rfl

end

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open PackingJobBody (nextInput pairRecords bodyTimePolynomial)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

def code (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (labelPower repetitionOne : α) (_distinctInput : labelPower ≠ repetitionOne)
    (leftPower rightPower one temp : Other) (otherDistinct : one ≠ temp)
    (output counter : Extra) :
    Code (K := PackingMachineLayout.Tape num den Other Extra) (S := State) :=
  PackingCountedProgram.loop (.inr counter)
    (PackingJobBody.body num den descriptors labelPower repetitionOne
      leftPower rightPower one temp otherDistinct output)

private theorem layout_counter (num : δ → Expr α) (den : Expr α)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (counter : Extra) (n : Nat) :
    tapes num den (counterTapes (.inr counter) base n) input other =
      counterTapes (.inr counter) (tapes num den base input other) n := by
  apply RegisterFrameEmission.external_update
  intro i
  simp [registers]

private theorem output_counter (num : δ → Expr α) (den : Expr α)
    (base : Tape num den Other Extra → List Bool) (output counter : Extra)
    (different : output ≠ counter) (word : List Bool) (n : Nat) :
    outputTapes (.inr output) (counterTapes (.inr counter) base n) word =
      counterTapes (.inr counter) (outputTapes (.inr output) base word) n := by
  funext k
  by_cases ho : k = .inr output
  · subst k
    simp [outputTapes, counterTapes, different]
  · by_cases hc : k = .inr counter
    · subst k
      simp [outputTapes, counterTapes, different, Ne.symm different]
    · simp [outputTapes, counterTapes, ho, hc]

private theorem exec_bounded (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (inputDifferent : power ≠ repetition)
    (leftPower rightPower one temp : Other) (different : one ≠ temp)
    (output counter : Extra) (outputCounter : output ≠ counter)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hone : other one = 1) (htemp : other temp = 0)
    (count width : Nat) (state : State)
    (hi : ∀ r, r ≤ count → ∀ a,
      (iterationInput input power repetition (other rightPower) r a).size ≤ width)
    (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ count * ((bodyTimePolynomial num den descriptors power
        leftPower rightPower).eval width + 1) + 1,
      Exec (code num den descriptors power repetition inputDifferent leftPower rightPower
          one temp different output counter)
        ⟨state, counterTapes (.inr counter) (tapes num den base input other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power repetition
                (other leftPower) (other rightPower) count))
            (iterationInput input power repetition (other rightPower) count) other) 0⟩ := by
  induction count generalizing input base state with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      have stop : PackingCountedProgram.more ((PackingCountedProgram.guard (.inr counter)).eval
          ⟨state, counterTapes (.inr counter) (tapes num den base input other) 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [code, PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        stream, iterationInput, PackingChunkMachine.outputTapes_nil] using
        (Exec.loop_false (a := PackingJobBody.body num den descriptors power repetition
          leftPower rightPower one temp different output) stop)
  | succ count ih =>
      let word := pairRecords num den descriptors input power (other leftPower) (other rightPower)
      let next := nextInput input power repetition (other rightPower)
      have initialWidth : ∀ a, (input a).size ≤ width := hi 0 (by omega)
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ :=
        PackingJobBody.body_exec num den descriptors power repetition inputDifferent
          leftPower rightPower one temp different output
          (counterTapes (.inr counter) base count) input other hone htemp width
          initialWidth ho (guardState (some true))
      rw [layout_counter, output_counter num den base output counter outputCounter,
        layout_counter] at bodyRun
      have tailWidth : ∀ r, r ≤ count → ∀ a,
          (iterationInput next power repetition (other rightPower) r a).size ≤ width := by
        intro r hr
        rw [iterationInput_succ input power repetition (other rightPower) inputDifferent r]
        exact hi (r + 1) (by omega)
      obtain ⟨tailSteps, tailBound, tailRun⟩ :=
        ih (outputTapes (.inr output) base word) next
          (.arithmetic (BinaryAddMachine.clean ())) tailWidth
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · rw [Nat.succ_mul]
        omega
      · have more : PackingCountedProgram.more
            ((PackingCountedProgram.guard (.inr counter)).eval
              ⟨state, counterTapes (.inr counter) (tapes num den base input other)
                (count + 1)⟩).state = true := by
          rw [PackingCountedProgram.guard_succ]
          rfl
        have bodyRun' : Exec (PackingJobBody.body num den descriptors power repetition
            leftPower rightPower one temp different output)
            ((PackingCountedProgram.guard (.inr counter)).eval
              ⟨state, counterTapes (.inr counter) (tapes num den base input other)
                (count + 1)⟩) bodySteps
            ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr counter)
              (tapes num den (outputTapes (.inr output) base word) next other) count⟩ := by
          rw [PackingCountedProgram.guard_succ]
          exact bodyRun
        have combined := Exec.loop_true more bodyRun' tailRun
        simpa only [code, PackingCountedProgram.loop, next, word, stream,
          PackingChunkMachine.outputTapes_append,
          iterationInput_succ input power repetition (other rightPower) inputDifferent count]
          using combined

theorem exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (inputDifferent : power ≠ repetition)
    (leftPower rightPower one temp : Other) (different : one ≠ temp)
    (output counter : Extra) (outputCounter : output ≠ counter)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hone : other one = 1) (htemp : other temp = 0)
    (count inputWidth otherWidth : Nat)
    (hi : ∀ a, (input a).size ≤ inputWidth) (ho : ∀ a, (other a).size ≤ otherWidth)
    (state : State) :
    ∃ steps ≤ count * ((bodyTimePolynomial num den descriptors power
        leftPower rightPower).eval (aggregateWidth inputWidth otherWidth count) + 1) + 1,
      Exec (code num den descriptors power repetition inputDifferent leftPower rightPower
          one temp different output counter)
        ⟨state, counterTapes (.inr counter) (tapes num den base input other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power repetition
                (other leftPower) (other rightPower) count))
            (iterationInput input power repetition (other rightPower) count) other) 0⟩ := by
  apply exec_bounded num den descriptors power repetition inputDifferent
    leftPower rightPower one temp different output counter outputCounter base input other
    hone htemp count (aggregateWidth inputWidth otherWidth count) state
  · intro r hr
    exact iterationInput_size_le input power repetition (other rightPower) inputDifferent
      inputWidth otherWidth count r hr hi (ho rightPower)
  · intro a
    have h := ho a
    unfold aggregateWidth
    omega

def timePolynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (leftPower rightPower : Other) : Polynomial Nat :=
  Polynomial.X * (bodyTimePolynomial num den descriptors power leftPower rightPower + 1) + 1

theorem exec_polynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (inputDifferent : power ≠ repetition)
    (leftPower rightPower one temp : Other) (different : one ≠ temp)
    (output counter : Extra) (outputCounter : output ≠ counter)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hone : other one = 1) (htemp : other temp = 0)
    (count inputWidth otherWidth : Nat)
    (hi : ∀ a, (input a).size ≤ inputWidth) (ho : ∀ a, (other a).size ≤ otherWidth)
    (state : State) :
    ∃ steps ≤ (timePolynomial num den descriptors power leftPower rightPower).eval
        (aggregateWidth inputWidth otherWidth count),
      Exec (code num den descriptors power repetition inputDifferent leftPower rightPower
          one temp different output counter)
        ⟨state, counterTapes (.inr counter) (tapes num den base input other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power repetition
                (other leftPower) (other rightPower) count))
            (iterationInput input power repetition (other rightPower) count) other) 0⟩ := by
  obtain ⟨steps, bound, run⟩ := exec num den descriptors power repetition inputDifferent
    leftPower rightPower one temp different output counter outputCounter base input other
    hone htemp count inputWidth otherWidth hi ho state
  refine ⟨steps, bound.trans ?_, run⟩
  have hc : count ≤ aggregateWidth inputWidth otherWidth count := by
    unfold aggregateWidth
    omega
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one] using
    Nat.add_le_add_right (Nat.mul_le_mul_right
      ((bodyTimePolynomial num den descriptors power leftPower rightPower).eval
        (aggregateWidth inputWidth otherWidth count) + 1) hc) 1

end BinPackingGap.PackingJobLoop

end

end OAI

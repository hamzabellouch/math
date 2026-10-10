import OAI.Computability.BinPacking.Arithmetic.GraphPackingRegisters

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPreparation

open GraphPackingRegisters PackingItemExpression

variable (fixed : InventoryData) (K : Nat)

def initialTapes (x : GraphReductionInput) : Tape fixed K → List Bool
  | .inr .input => graphBits x
  | _ => []

def baseTapes (x : GraphReductionInput) (reverseOutput : List Bool := []) :
    Tape fixed K → List Bool
  | .inr .input => graphBits x
  | .inr .endpoints => GraphFieldMachine.fieldBits .endpoints x
  | .inr .reverseOutput => reverseOutput
  | _ => []

def parsedOther (x : GraphReductionInput) : Other fixed K → Nat
  | .inl r => PackingSetupMachine.frame (parameters fixed K)
      (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k) (fun _ => 0) r
  | .inr _ => 0

def parsedTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingMachineLayout.tapes (Numerator fixed) denominator
    (baseTapes fixed K x) (fun _ => 0) (parsedOther fixed K x)

def setupOther (x : GraphReductionInput) (workValues : Work → Nat := fun _ => 0) :
    Other fixed K → Nat
  | .inl r => PackingSetupMachine.frame (parameters fixed K)
      (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k)
      (PackingSetupExpression.outputValues (parameters fixed K)
        x.graph.n x.graph.edges.length x.k) r
  | .inr r => workValues r

def repetitions (x : GraphReductionInput) : Nat :=
  100 * (fixed.P + x.graph.n * K + 1)

def geometryFactor : Nat :=
  160 * IntegerPackingArithmetic.widthRadix fixed.geometryBound ^ fixed.L

def preparedInputs (x : GraphReductionInput) : Variable → Nat
  | .vertexPower => 3 ^ x.graph.n
  | .totalPower => (repetitions fixed K x + 1) ^ x.graph.edges.length
  | .geometry => geometryFactor fixed *
      (repetitions fixed K x + 1) ^ x.graph.edges.length
  | _ => 0

def preparedWork : Work → Nat
  | .geometryFactor => geometryFactor fixed
  | _ => 0

def preparedOther (x : GraphReductionInput) : Other fixed K → Nat :=
  setupOther fixed K x (preparedWork fixed)

def binBound (x : GraphReductionInput) : Nat :=
  PackingSetupExpression.outputValues (parameters fixed K)
    x.graph.n x.graph.edges.length x.k .bins

def preparedTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingMachineLayout.tapes (Numerator fixed) denominator
    (baseTapes fixed K x (BinaryEncoding.natBits (binBound fixed K x)).reverse)
    (preparedInputs fixed K x) (preparedOther fixed K x)

end BinPackingGap.GraphPackingPreparation

namespace BinPackingGap.GraphPackingJobStream

open PackingDescriptorExpression PackingInventoryDescriptors

def endpointPower (D : InventoryData) (edge : D.Edge) (side : Fin 2) : Nat :=
  3 ^ ((D.graph.endpoint edge side).val + 1)

theorem values_update_label (D : InventoryData) (label : Option D.Vertex)
    (vertex : D.Vertex) (edge rep : Nat) :
    Function.update (values D label edge rep) .labelPower (3 ^ (vertex.val + 1)) =
      values D (some vertex) edge rep := by
  funext slot
  cases slot <;> simp [values, NaturalPackingNumerator.labelPower]

theorem nextInput_values (D : InventoryData) (label : Option D.Vertex)
    (edge : D.Edge) (rep : Nat) :
    PackingJobBody.nextInput (values D label edge.val rep) .labelPower .repetitionOne
        (endpointPower D edge 1) =
      values D (some (D.graph.endpoint edge 1)) edge.val (rep + 1) := by
  funext slot
  cases slot <;>
    simp [PackingJobBody.nextInput, values, endpointPower,
      NaturalPackingNumerator.labelPower]

def rawPair (D : InventoryData) (edge : D.Edge) (rep : Nat) : RawInstance :=
  (List.finRange 2).flatMap fun side =>
    (jobDescriptors D).map
      (rawOfDescriptor D (some (D.graph.endpoint edge side)) edge.val rep)

theorem pairRecords_eq (D : InventoryData) (label : Option D.Vertex)
    (edge : D.Edge) (rep : Nat) :
    PackingJobBody.pairRecords (numerator D) PackingItemExpression.denominator
        (jobDescriptors D) (values D label edge.val rep) .labelPower
        (endpointPower D edge 0) (endpointPower D edge 1) =
      rawRecords (rawPair D edge rep) := by
  have sides : List.finRange 2 = [0, 1] := by decide
  unfold PackingJobBody.pairRecords endpointPower
  rw [values_update_label, values_update_label, chunk_records, chunk_records]
  simp only [rawPair, sides, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, rawRecords, List.flatMap_append]

theorem stream_eq (D : InventoryData) (edge : D.Edge) (count rep : Nat)
    (label : Option D.Vertex) :
    PackingJobLoop.stream (numerator D) PackingItemExpression.denominator
        (jobDescriptors D) (values D label edge.val rep) .labelPower .repetitionOne
        (endpointPower D edge 0) (endpointPower D edge 1) count =
      rawRecords ((List.finRange count).flatMap fun j => rawPair D edge (rep + j.val)) := by
  induction count generalizing rep label with
  | zero => simp [PackingJobLoop.stream, rawRecords]
  | succ count ih =>
      rw [PackingJobLoop.stream_succ, pairRecords_eq, nextInput_values, ih]
      have order : (List.finRange (count + 1)).flatMap
          (fun j => rawPair D edge (rep + j.val)) =
          rawPair D edge rep ++ (List.finRange count).flatMap
            (fun j => rawPair D edge ((rep + 1) + j.val)) := by
        rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
        simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
        congr 1
        apply congrArg (fun f => (List.finRange count).flatMap f)
        funext j
        congr 1
        omega
      rw [order]
      simp only [rawRecords, List.flatMap_append]

theorem stream_edge_eq (D : InventoryData) (edge : D.Edge) (label : Option D.Vertex) :
    PackingJobLoop.stream (numerator D) PackingItemExpression.denominator
        (jobDescriptors D) (values D label edge.val 1) .labelPower .repetitionOne
        (endpointPower D edge 0) (endpointPower D edge 1) D.R =
      rawRecords ((List.finRange D.R).flatMap fun j =>
        (List.finRange 2).flatMap fun side =>
          (jobDescriptors D).map
            (rawOfDescriptor D (some (D.graph.endpoint edge side)) edge.val (j.val + 1))) := by
  simpa only [rawPair, Nat.add_comm 1] using stream_eq D edge D.R 1 label

theorem all_edges_eq (D : InventoryData) (label : Option D.Vertex) :
    (List.finRange D.graph.edges.length).flatMap (fun edge =>
      PackingJobLoop.stream (numerator D) PackingItemExpression.denominator
        (jobDescriptors D) (values D label edge.val 1) .labelPower .repetitionOne
        (endpointPower D edge 0) (endpointPower D edge 1) D.R) =
      rawRecords (jobStream D) := by
  simp_rw [stream_edge_eq]
  simp only [jobStream, rawRecords, List.flatMap_assoc]

theorem stream_edge_instantiate_eq (fixed : InventoryData) (graph : GraphInput)
    (R k : Nat) (edge : graph.Edge) (label : Option graph.Vertex) :
    PackingJobLoop.stream (numerator fixed) PackingItemExpression.denominator
        (jobDescriptors fixed) (values (instantiate fixed graph R k) label edge.val 1)
        .labelPower .repetitionOne
        (endpointPower (instantiate fixed graph R k) edge 0)
        (endpointPower (instantiate fixed graph R k) edge 1) R =
      rawRecords ((List.finRange R).flatMap fun j =>
        (List.finRange 2).flatMap fun side =>
          (jobDescriptors fixed).map (rawOfDescriptor (instantiate fixed graph R k)
            (some (graph.endpoint edge side)) edge.val (j.val + 1))) := by
  have hnum : numerator (instantiate fixed graph R k) = numerator fixed := by
    funext descriptor
    exact numerator_instantiate fixed graph R k descriptor
  have hstream := stream_edge_eq (instantiate fixed graph R k) edge label
  simp only [jobDescriptors_instantiate, hnum] at hstream
  simpa only [instantiate] using hstream

end BinPackingGap.GraphPackingJobStream

namespace BinPackingGap.GraphPackingWidths

open GraphPackingRegisters GraphPackingPreparation
open BinaryRegisterProgram

variable (fixed : InventoryData) (K : Nat)

def treeScale : Nat := IntegerPackingArithmetic.widthRadix fixed.geometryBound ^ fixed.L

def setupPolynomial : Polynomial Nat :=
  Polynomial.C (2 ^ (PackingSetupMachine.commands (parameters fixed K)).length) *
    (Polynomial.X + Polynomial.C (maxConstantSize (PackingSetupMachine.commands
      (parameters fixed K)) + 1))

theorem setupPolynomial_eval (s : Nat) :
    (setupPolynomial fixed K).eval s = staticWidth
      (PackingSetupMachine.commands (parameters fixed K)) s := by
  simp only [setupPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X, staticWidth, Nat.add_assoc]

def geometryCoefficient : Nat :=
  GraphPackingBounds.repetitionCoefficient fixed.P K + 2 +
    Nat.size 160 + Nat.size (treeScale fixed)

def polynomial : Polynomial Nat :=
  setupPolynomial fixed K +
    Polynomial.C (geometryCoefficient fixed K) * (Polynomial.X + 1) ^ 2 +
    Polynomial.C (GraphPackingBounds.repetitionCoefficient fixed.P K + 3) *
      (Polynomial.X + 1) +
    Polynomial.C ((geometryFactor fixed).size + 5)

theorem polynomial_eval (s : Nat) :
    (polynomial fixed K).eval s = (setupPolynomial fixed K).eval s +
      geometryCoefficient fixed K * (s + 1) ^ 2 +
      (GraphPackingBounds.repetitionCoefficient fixed.P K + 3) * (s + 1) +
      (geometryFactor fixed).size + 5 := by
  simp [polynomial]
  omega

def width (x : GraphReductionInput) : Nat := (polynomial fixed K).eval (graphBits x).length

theorem setup_width (x : GraphReductionInput) :
    ∀ r, (PackingSetupMachine.frame (parameters fixed K)
      (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k)
      (PackingSetupExpression.outputValues (parameters fixed K)
        x.graph.n x.graph.edges.length x.k) r).size ≤ width fixed K x := by
  let p := parameters fixed K
  let initial := PackingSetupMachine.frame p
    (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k) (fun _ => 0)
  have hi : ∀ r, (initial r).size ≤ (graphBits x).length := by
    intro r
    rcases r with a | (o | temp)
    · cases a with
      | n => exact (nat_size_le_self _).trans (graph_vertexCount_le_bits x)
      | m => exact (nat_size_le_self _).trans (graph_edgeCount_le_bits x)
      | k =>
          exact (nat_size_le_self _).trans
            (x.k_le.trans (graph_vertexCount_le_bits x))
    · simp [initial, PackingSetupMachine.frame]
    · simp [initial, PackingSetupMachine.frame]
  have h := BinaryRegisterStructured.final_width (PackingSetupMachine.commands p) initial
    (graphBits x).length hi
  rw [(PackingSetupMachine.commands_correct p x.graph.n x.graph.edges.length x.k).2] at h
  intro r
  have hr := h r
  rw [← setupPolynomial_eval fixed K] at hr
  unfold width
  rw [polynomial_eval]
  exact hr.trans (by omega)

theorem geometry_width (x : GraphReductionInput) :
    (geometryFactor fixed * (GraphPackingPreparation.repetitions fixed K x + 1) ^ x.graph.edges.length).size ≤
      width fixed K x := by
  have h := GraphPackingBounds.size_geometry_denominator_le_quadratic fixed.P K
    (treeScale fixed) x.graph.n x.graph.edges.length (graphBits x).length
    (graph_vertexCount_le_bits x) (graph_edgeCount_le_bits x)
  have heq : geometryFactor fixed * (GraphPackingPreparation.repetitions fixed K x + 1) ^ x.graph.edges.length =
      160 * (100 * (fixed.P + x.graph.n * K + 1) + 1) ^ x.graph.edges.length *
        treeScale fixed := by
    unfold geometryFactor GraphPackingPreparation.repetitions treeScale
    ring
  rw [heq]
  change _ ≤ geometryCoefficient fixed K * ((graphBits x).length + 1) ^ 2 at h
  unfold width
  rw [polynomial_eval]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at h ⊢
  omega

theorem edge_power_width (x : GraphReductionInput) (edge : Nat)
    (he : edge ≤ x.graph.edges.length) :
    ((GraphPackingPreparation.repetitions fixed K x + 1) ^ edge).size ≤ width fixed K x := by
  have h := GraphPackingBounds.size_edge_power_le_quadratic fixed.P K x.graph.n edge
    (graphBits x).length (graph_vertexCount_le_bits x) (he.trans (graph_edgeCount_le_bits x))
  unfold GraphPackingPreparation.repetitions
  unfold width
  rw [polynomial_eval]
  have hcoeff : GraphPackingBounds.repetitionCoefficient fixed.P K + 2 ≤
      geometryCoefficient fixed K := by unfold geometryCoefficient; omega
  have hm := Nat.mul_le_mul_right (((graphBits x).length + 1) ^ 2) hcoeff
  omega

theorem vertex_power_width (x : GraphReductionInput) (vertex : Nat)
    (hv : vertex ≤ x.graph.n + 1) :
    (3 ^ vertex).size ≤ width fixed K x := by
  have hn : vertex ≤ (graphBits x).length + 1 := by
    have h := graph_vertexCount_le_bits x
    omega
  have h := GraphPackingBounds.size_vertex_power_le_linear vertex ((graphBits x).length + 1) hn
  unfold width
  rw [polynomial_eval]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at h ⊢
  omega

theorem preparedInputs_width (x : GraphReductionInput) :
    ∀ a, (preparedInputs fixed K x a).size ≤ width fixed K x := by
  intro a
  cases a with
  | vertexPower => exact vertex_power_width fixed K x x.graph.n (by omega)
  | geometry => exact geometry_width fixed K x
  | totalPower => exact edge_power_width fixed K x x.graph.edges.length le_rfl
  | labelPower => simp [preparedInputs]
  | edgePower => simp [preparedInputs]
  | repetitionOne => simp [preparedInputs]

theorem preparedWork_width (x : GraphReductionInput) :
    ∀ r, (preparedWork fixed r).size ≤ width fixed K x := by
  intro r
  cases r <;> simp only [preparedWork, Nat.size_zero]
  all_goals unfold width; rw [polynomial_eval]; omega

theorem preparedOther_width (x : GraphReductionInput) :
    ∀ r, (preparedOther fixed K x r).size ≤ width fixed K x := by
  intro r
  cases r with
  | inl r => exact setup_width fixed K x r
  | inr r => exact preparedWork_width fixed K x r

theorem partial_inputs_width (x : GraphReductionInput) (input : PackingItemExpression.Variable → Nat)
    (hle : ∀ a, input a ≤ preparedInputs fixed K x a) :
    ∀ a, (input a).size ≤ width fixed K x := by
  intro a
  exact (nat_size_mono (hle a)).trans (preparedInputs_width fixed K x a)

theorem repetitions_width (x : GraphReductionInput) :
    GraphPackingPreparation.repetitions fixed K x + 1 ≤ width fixed K x := by
  have h := GraphPackingBounds.repetitions_le_linear fixed.P K x.graph.n (graphBits x).length
    (graph_vertexCount_le_bits x)
  change GraphPackingPreparation.repetitions fixed K x ≤ _ at h
  unfold width
  rw [polynomial_eval]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at h ⊢
  omega

theorem small_constant_width (x : GraphReductionInput) : 3 ≤ width fixed K x := by
  unfold width
  rw [polynomial_eval]
  omega

theorem input_length_le_width (x : GraphReductionInput) :
    (graphBits x).length + 1 ≤ width fixed K x := by
  unfold width
  rw [polynomial_eval]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem update_width {α : Type} [DecidableEq α] (x : GraphReductionInput)
    (values : α → Nat) (h : ∀ a, (values a).size ≤ width fixed K x)
    (a : α) (v : Nat) (hv : v.size ≤ width fixed K x) :
    ∀ b, (Function.update values a v b).size ≤ width fixed K x := by
  intro b
  by_cases hb : b = a
  · subst b; simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne hb] using h b

end BinPackingGap.GraphPackingWidths

namespace BinPackingGap.GraphPackingJobs

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression

variable (fixed : InventoryData) (K : Nat)

def inventory (x : GraphReductionInput) : InventoryData :=
  PackingDescriptorExpression.instantiate fixed x.graph
    (GraphPackingPreparation.repetitions fixed K x) x.k

def inputs (x : GraphReductionInput) (edge : Nat) : Variable → Nat :=
  Function.update (preparedInputs fixed K x) .edgePower
    ((GraphPackingPreparation.repetitions fixed K x + 1) ^ edge)

@[simp] theorem inputs_label (x : GraphReductionInput) (edge : Nat) :
    inputs fixed K x edge .labelPower = 0 := rfl

@[simp] theorem inputs_repetition (x : GraphReductionInput) (edge : Nat) :
    inputs fixed K x edge .repetitionOne = 0 := rfl

@[simp] theorem inputs_edge (x : GraphReductionInput) (edge : Nat) :
    inputs fixed K x edge .edgePower =
      (GraphPackingPreparation.repetitions fixed K x + 1) ^ edge := by
  simp [inputs]

theorem inputs_eq_values (x : GraphReductionInput) (edge : Nat) :
    inputs fixed K x edge = PackingDescriptorExpression.values (inventory fixed K x) none edge 0 := by
  funext coordinate
  cases coordinate <;>
    simp [inputs, preparedInputs, PackingDescriptorExpression.values, inventory,
      PackingDescriptorExpression.instantiate, NaturalPackingNumerator.labelPower,
      InventoryData.coordinateDenominator, IntegerPackingArithmetic.geomDenominator,
      geometryFactor, InventoryData.geometryBound, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

def endpointWork (right : Bool) : Work := if right then .rightEndpoint else .leftEndpoint
def powerWork (right : Bool) : Work := if right then .rightPower else .leftPower

def loadEndpoint (other : Other fixed K → Nat) (right : Bool) (v : Nat) : Other fixed K → Nat :=
  Function.update (Function.update other (.inr (endpointWork right)) v)
    (.inr (powerWork right)) (3 ^ (v + 1))

def loadedOther (x : GraphReductionInput) (left right : Nat) : Other fixed K → Nat :=
  loadEndpoint fixed K (loadEndpoint fixed K (preparedOther fixed K x) false left) true right

@[simp] theorem loaded_left (x : GraphReductionInput) (left right : Nat) :
    loadedOther fixed K x left right (.inr .leftPower) = 3 ^ (left + 1) := by
  simp [loadedOther, loadEndpoint, endpointWork, powerWork]

@[simp] theorem loaded_right (x : GraphReductionInput) (left right : Nat) :
    loadedOther fixed K x left right (.inr .rightPower) = 3 ^ (right + 1) := by
  simp [loadedOther, loadEndpoint, endpointWork, powerWork]

theorem inputs_width (x : GraphReductionInput) (edge : Nat) (he : edge ≤ x.graph.edges.length) :
    ∀ a, (inputs fixed K x edge a).size ≤ GraphPackingWidths.width fixed K x :=
  GraphPackingWidths.update_width fixed K x _
    (GraphPackingWidths.preparedInputs_width fixed K x) .edgePower _
    (GraphPackingWidths.edge_power_width fixed K x edge he)

theorem loadEndpoint_width (x : GraphReductionInput) (other : Other fixed K → Nat)
    (hother : ∀ r, (other r).size ≤ GraphPackingWidths.width fixed K x)
    (right : Bool) (v : Nat) (hv : v < x.graph.n) :
    ∀ r, (loadEndpoint fixed K other right v r).size ≤ GraphPackingWidths.width fixed K x := by
  have hvsize : v.size ≤ GraphPackingWidths.width fixed K x :=
    (nat_size_le_self v).trans
      ((Nat.le_of_lt hv).trans ((graph_vertexCount_le_bits x).trans
        ((Nat.le_succ _).trans (GraphPackingWidths.input_length_le_width fixed K x))))
  apply GraphPackingWidths.update_width fixed K x
  · exact GraphPackingWidths.update_width fixed K x other hother _ v hvsize
  · exact GraphPackingWidths.vertex_power_width fixed K x (v + 1) (by omega)

theorem loadedOther_width (x : GraphReductionInput) (left right : Nat)
    (hl : left < x.graph.n) (hr : right < x.graph.n) :
    ∀ r, (loadedOther fixed K x left right r).size ≤ GraphPackingWidths.width fixed K x := by
  exact loadEndpoint_width fixed K x _
    (loadEndpoint_width fixed K x _ (GraphPackingWidths.preparedOther_width fixed K x)
      false left hl) true right hr

theorem loaded_setup (x : GraphReductionInput) (left right : Nat)
    (r : PackingSetupMachine.Reg (parameters fixed K)) :
    loadedOther fixed K x left right (.inl r) = preparedOther fixed K x (.inl r) := by
  simp [loadedOther, loadEndpoint]

theorem loaded_helper_zero (x : GraphReductionInput) (left right : Nat) (w : Work)
    (hw : w = .counter ∨ w = .one ∨ w = .temporary ∨ w = .reverse) :
    loadedOther fixed K x left right (.inr w) = 0 := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp [loadedOther, loadEndpoint, endpointWork, powerWork, preparedOther,
      setupOther, preparedWork]

def completedInputs (x : GraphReductionInput) (edge right : Nat) : Variable → Nat :=
  Function.update (Function.update (inputs fixed K x edge) .labelPower (3 ^ (right + 1)))
    .repetitionOne (GraphPackingPreparation.repetitions fixed K x + 1)

theorem completedInputs_width (x : GraphReductionInput) (edge right : Nat)
    (he : edge ≤ x.graph.edges.length) (hr : right < x.graph.n) :
    ∀ a, (completedInputs fixed K x edge right a).size ≤ GraphPackingWidths.width fixed K x := by
  apply GraphPackingWidths.update_width fixed K x
  · exact GraphPackingWidths.update_width fixed K x _ (inputs_width fixed K x edge he)
      .labelPower _ (GraphPackingWidths.vertex_power_width fixed K x (right + 1) (by omega))
  · exact (nat_size_le_self _).trans (GraphPackingWidths.repetitions_width fixed K x)

def clearedOther (x : GraphReductionInput) (left right : Nat) : Other fixed K → Nat :=
  Function.update (Function.update (Function.update (Function.update
    (loadedOther fixed K x left right) (.inr .leftEndpoint) 0) (.inr .rightEndpoint) 0)
      (.inr .leftPower) 0) (.inr .rightPower) 0

theorem clearedOther_eq (x : GraphReductionInput) (left right : Nat) :
    clearedOther fixed K x left right = preparedOther fixed K x := by
  funext r
  cases r with
  | inl r => simp [clearedOther, loadedOther, loadEndpoint]
  | inr r =>
      cases r <;> simp [clearedOther, loadedOther, loadEndpoint, endpointWork, powerWork,
        preparedOther, setupOther, preparedWork]

theorem clearedInputs_eq (x : GraphReductionInput) (edge right : Nat) :
    Function.update (Function.update (Function.update (completedInputs fixed K x edge right)
      .edgePower ((GraphPackingPreparation.repetitions fixed K x + 1) ^ (edge + 1)))
      .labelPower 0) .repetitionOne 0 =
      inputs fixed K x (edge + 1) := by
  funext a
  cases a <;> simp [completedInputs, inputs, preparedInputs]

end BinPackingGap.GraphPackingJobs

namespace BinPackingGap.GraphPackingStockBounds

open scoped BigOperators

variable (fixed : InventoryData) (K : Nat)

def inventory (x : GraphReductionInput) : InventoryData :=
  PackingDescriptorExpression.instantiate fixed x.graph
    (GraphPackingPreparation.repetitions fixed K x) x.k

def stockCoefficient : Nat :=
  GraphPackingBounds.binCoefficient fixed.P K fixed.t fixed.d

def stockPolynomial : Polynomial Nat :=
  Polynomial.C (stockCoefficient fixed K) * (Polynomial.X + 1) ^ 2

@[simp] theorem stockPolynomial_eval (s : Nat) :
    (stockPolynomial fixed K).eval s = stockCoefficient fixed K * (s + 1) ^ 2 := by
  simp [stockPolynomial]

theorem binCount_le (x : GraphReductionInput) :
    (inventory fixed K x).B ≤ stockCoefficient fixed K * ((graphBits x).length + 1) ^ 2 := by
  rw [InventoryData.B_closed]
  exact GraphPackingBounds.bins_le_quadratic fixed.P K x.graph.n x.graph.edges.length
    fixed.t fixed.d (graphBits x).length
    (graph_vertexCount_le_bits x) (graph_edgeCount_le_bits x)

theorem globalStock_le (x : GraphReductionInput) (species : GlobalSpecies x.graph) :
    (inventory fixed K x).globalStock species ≤
      stockCoefficient fixed K * ((graphBits x).length + 1) ^ 2 := by
  let D := inventory fixed K x
  have hsum : (∑ s, D.globalStock s) = D.B := by
    simpa only [InventoryData.GlobalCopy, Fintype.card_sigma, Fintype.card_fin]
      using D.card_globalCopy x.k_le
  have hstock : D.globalStock species ≤ ∑ s, D.globalStock s :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ species)
  exact (hstock.trans_eq hsum).trans (binCount_le fixed K x)

theorem flagStock_le (x : GraphReductionInput) (species : FlagSpecies) :
    (inventory fixed K x).flagStock species ≤
      stockCoefficient fixed K * ((graphBits x).length + 1) ^ 2 := by
  let D := inventory fixed K x
  have hsum : (∑ s, D.flagStock s) = D.B := by
    simpa only [InventoryData.FlagCopy, Fintype.card_sigma, Fintype.card_fin]
      using D.card_flagCopy
  have hstock : D.flagStock species ≤ ∑ s, D.flagStock s :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ species)
  exact (hstock.trans_eq hsum).trans (binCount_le fixed K x)

theorem globalStock_le_polynomial (x : GraphReductionInput)
    (species : GlobalSpecies x.graph) :
    (inventory fixed K x).globalStock species ≤
      (stockPolynomial fixed K).eval (graphBits x).length := by
  rw [stockPolynomial_eval]
  exact globalStock_le fixed K x species

theorem flagStock_le_polynomial (x : GraphReductionInput) (species : FlagSpecies) :
    (inventory fixed K x).flagStock species ≤
      (stockPolynomial fixed K).eval (graphBits x).length := by
  rw [stockPolynomial_eval]
  exact flagStock_le fixed K x species

def setupCoefficient : Nat :=
  2 ^ (PackingSetupMachine.commands (GraphPackingRegisters.parameters fixed K)).length *
    (BinaryRegisterProgram.maxConstantSize
      (PackingSetupMachine.commands (GraphPackingRegisters.parameters fixed K)) + 2)

def widthCoefficient : Nat :=
  setupCoefficient fixed K + GraphPackingWidths.geometryCoefficient fixed K +
    (GraphPackingBounds.repetitionCoefficient fixed.P K + 3) +
    ((GraphPackingPreparation.geometryFactor fixed).size + 5)

def widthPolynomial : Polynomial Nat :=
  Polynomial.C (widthCoefficient fixed K) * (Polynomial.X + 1) ^ 2

@[simp] theorem widthPolynomial_eval (s : Nat) :
    (widthPolynomial fixed K).eval s = widthCoefficient fixed K * (s + 1) ^ 2 := by
  simp [widthPolynomial]

private theorem setupPolynomial_le (s : Nat) :
    (GraphPackingWidths.setupPolynomial fixed K).eval s ≤
      setupCoefficient fixed K * (s + 1) ^ 2 := by
  let commands := PackingSetupMachine.commands (GraphPackingRegisters.parameters fixed K)
  let c := BinaryRegisterProgram.maxConstantSize commands
  have hs : s + (c + 1) ≤ (c + 2) * (s + 1) := by nlinarith
  simp only [GraphPackingWidths.setupPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X]
  change 2 ^ commands.length * (s + (c + 1)) ≤
    (2 ^ commands.length * (c + 2)) * (s + 1) ^ 2
  calc
    _ ≤ 2 ^ commands.length * ((c + 2) * (s + 1)) :=
      Nat.mul_le_mul_left _ hs
    _ = (2 ^ commands.length * (c + 2)) * (s + 1) := by ring
    _ ≤ _ := GraphPackingBounds.linear_le_quadratic _ s

theorem preparationPolynomial_le (s : Nat) :
    (GraphPackingWidths.polynomial fixed K).eval s ≤
      widthCoefficient fixed K * (s + 1) ^ 2 := by
  have hsetup := setupPolynomial_le fixed K s
  have hlinear := GraphPackingBounds.linear_le_quadratic
    (GraphPackingBounds.repetitionCoefficient fixed.P K + 3) s
  have hconstant := GraphPackingBounds.constant_le_quadratic
    ((GraphPackingPreparation.geometryFactor fixed).size + 5) s
  rw [GraphPackingWidths.polynomial_eval]
  unfold widthCoefficient
  nlinarith

theorem preparationWidth_le (x : GraphReductionInput) :
    GraphPackingWidths.width fixed K x ≤
      widthCoefficient fixed K * ((graphBits x).length + 1) ^ 2 :=
  preparationPolynomial_le fixed K (graphBits x).length

theorem values_width (x : GraphReductionInput) (edge : Nat)
    (he : edge ≤ x.graph.edges.length) (vinput : PackingItemExpression.Variable) :
    (PackingDescriptorExpression.values (inventory fixed K x) none edge 0 vinput).size ≤
      GraphPackingWidths.width fixed K x := by
  cases vinput with
  | vertexPower =>
      exact GraphPackingWidths.vertex_power_width fixed K x x.graph.n (by omega)
  | geometry =>
      change (160 * (GraphPackingPreparation.repetitions fixed K x + 1) ^
        x.graph.edges.length *
        IntegerPackingArithmetic.widthRadix fixed.geometryBound ^ fixed.L).size ≤ _
      have h := GraphPackingWidths.geometry_width fixed K x
      rw [GraphPackingPreparation.geometryFactor, Nat.mul_right_comm] at h
      exact h
  | labelPower =>
      simp [PackingDescriptorExpression.values, NaturalPackingNumerator.labelPower]
  | totalPower =>
      exact GraphPackingWidths.edge_power_width fixed K x x.graph.edges.length le_rfl
  | edgePower => exact GraphPackingWidths.edge_power_width fixed K x edge he
  | repetitionOne => simp [PackingDescriptorExpression.values]

theorem values_size_le (x : GraphReductionInput) (edge : Nat)
    (he : edge ≤ x.graph.edges.length) (vinput : PackingItemExpression.Variable) :
    (PackingDescriptorExpression.values (inventory fixed K x) none edge 0 vinput).size ≤
      widthCoefficient fixed K * ((graphBits x).length + 1) ^ 2 :=
  (values_width fixed K x edge he vinput).trans (preparationWidth_le fixed K x)

theorem values_size_le_polynomial (x : GraphReductionInput) (edge : Nat)
    (he : edge ≤ x.graph.edges.length) (vinput : PackingItemExpression.Variable) :
    (PackingDescriptorExpression.values (inventory fixed K x) none edge 0 vinput).size ≤
      (widthPolynomial fixed K).eval (graphBits x).length := by
  rw [widthPolynomial_eval]
  exact values_size_le fixed K x edge he vinput

theorem preparedOther_size_le (x : GraphReductionInput)
    (register : GraphPackingRegisters.Other fixed K) :
    (GraphPackingPreparation.preparedOther fixed K x register).size ≤
      widthCoefficient fixed K * ((graphBits x).length + 1) ^ 2 :=
  (GraphPackingWidths.preparedOther_width fixed K x register).trans
    (preparationWidth_le fixed K x)

theorem preparedOther_size_le_polynomial (x : GraphReductionInput)
    (register : GraphPackingRegisters.Other fixed K) :
    (GraphPackingPreparation.preparedOther fixed K x register).size ≤
      (widthPolynomial fixed K).eval (graphBits x).length := by
  rw [widthPolynomial_eval]
  exact preparedOther_size_le fixed K x register

end BinPackingGap.GraphPackingStockBounds

namespace BinPackingGap.GraphPackingJobs

section

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open PackingDescriptorExpression PackingInventoryDescriptors

variable (fixed : InventoryData) (K : Nat)

def repeatInputs (x : GraphReductionInput) (edge : Nat) : Variable → Nat :=
  Function.update (inputs fixed K x edge) .repetitionOne 1

def repeatFinalInputs (x : GraphReductionInput) (e : x.graph.Edge) : Variable → Nat :=
  completedInputs fixed K x e.val (x.graph.right e).val

def edgeWord (x : GraphReductionInput) (e : x.graph.Edge) : List Bool :=
  rawRecords ((List.finRange (GraphPackingPreparation.repetitions fixed K x)).flatMap fun j =>
    (List.finRange 2).flatMap fun side =>
      (jobDescriptors fixed).map
        (rawOfDescriptor (inventory fixed K x) (some (x.graph.endpoint e side))
          e.val (j.val + 1)))

@[simp] theorem repeatInputs_repetition (x : GraphReductionInput) (edge : Nat) :
    repeatInputs fixed K x edge .repetitionOne = 1 := by
  simp [repeatInputs]

theorem repeatInputs_eq_values (x : GraphReductionInput) (edge : Nat) :
    repeatInputs fixed K x edge = values (inventory fixed K x) none edge 1 := by
  unfold repeatInputs
  rw [inputs_eq_values]
  funext reg
  cases reg <;> simp [PackingDescriptorExpression.values]

theorem repeatInputs_width (x : GraphReductionInput) (edge : Nat)
    (he : edge ≤ x.graph.edges.length) :
    ∀ a, (repeatInputs fixed K x edge a).size ≤ GraphPackingWidths.width fixed K x := by
  apply GraphPackingWidths.update_width fixed K x _ (inputs_width fixed K x edge he)
    .repetitionOne 1
  simp only [Nat.size_one]
  have h := GraphPackingWidths.small_constant_width fixed K x
  omega

theorem repeatFinalInputs_width (x : GraphReductionInput) (e : x.graph.Edge) :
    ∀ a, (repeatFinalInputs fixed K x e a).size ≤ GraphPackingWidths.width fixed K x :=
  completedInputs_width fixed K x e.val (x.graph.right e).val
    (Nat.le_of_lt e.isLt) (x.graph.right e).isLt

theorem loaded_one (x : GraphReductionInput) (left right : Nat) :
    loadedOther fixed K x left right
        (.inl (PackingSetupMachine.output (parameters fixed K) .one)) = 1 := by
  rw [loaded_setup]
  rfl

theorem loaded_repetitions (x : GraphReductionInput) (left right : Nat) :
    loadedOther fixed K x left right
        (.inl (PackingSetupMachine.output (parameters fixed K) .repetitions)) =
      GraphPackingPreparation.repetitions fixed K x := by
  rw [loaded_setup]
  rfl

theorem repeatStream_eq (x : GraphReductionInput) (e : x.graph.Edge) :
    PackingJobLoop.stream (numerator fixed) denominator (jobDescriptors fixed)
        (repeatInputs fixed K x e.val) .labelPower .repetitionOne
        (loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val (.inr .leftPower))
        (loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val (.inr .rightPower))
        (GraphPackingPreparation.repetitions fixed K x) =
      edgeWord fixed K x e := by
  rw [repeatInputs_eq_values, loaded_left, loaded_right]
  simpa only [edgeWord, inventory, GraphPackingJobStream.endpointPower,
    PackingDescriptorExpression.instantiate, GraphInput.endpoint_zero, GraphInput.endpoint_one] using
    GraphPackingJobStream.stream_edge_instantiate_eq fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k e none

theorem repeatIteration_eq (x : GraphReductionInput) (e : x.graph.Edge) :
    PackingJobLoop.iterationInput (repeatInputs fixed K x e.val) .labelPower .repetitionOne
        (loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val (.inr .rightPower))
        (GraphPackingPreparation.repetitions fixed K x) =
      repeatFinalInputs fixed K x e := by
  have positive : 0 < GraphPackingPreparation.repetitions fixed K x := by
    unfold GraphPackingPreparation.repetitions
    omega
  rw [loaded_right]
  cases hcount : GraphPackingPreparation.repetitions fixed K x with
  | zero => omega
  | succ count =>
      funext reg
      cases reg <;>
        simp [PackingJobLoop.iterationInput, hcount, repeatInputs,
          repeatFinalInputs, completedInputs, Nat.add_comm]

end

open BinaryEncoding PackingDescriptorExpression PackingInventoryDescriptors

def edgeFields (x : GraphReductionInput) (es : List x.graph.Edge) : List Bool :=
  listBits (fun e => natBits (x.graph.left e).val ++ natBits (x.graph.right e).val) es

def edgeWords (fixed : InventoryData) (K : Nat) (x : GraphReductionInput)
    (es : List x.graph.Edge) : List Bool :=
  es.flatMap (edgeWord fixed K x)

@[simp] theorem edgeFields_nil (x : GraphReductionInput) :
    edgeFields x [] = [false] := rfl

theorem edgeFields_cons (x : GraphReductionInput) (e : x.graph.Edge)
    (es : List x.graph.Edge) :
    edgeFields x (e :: es) =
      true :: (natBits (x.graph.left e).val ++ natBits (x.graph.right e).val ++
        edgeFields x es) := by
  simp only [edgeFields, listBits, List.append_assoc]

@[simp] theorem edgeWords_nil (fixed : InventoryData) (K : Nat)
    (x : GraphReductionInput) : edgeWords fixed K x [] = [] := rfl

theorem edgeWords_cons (fixed : InventoryData) (K : Nat)
    (x : GraphReductionInput) (e : x.graph.Edge) (es : List x.graph.Edge) :
    edgeWords fixed K x (e :: es) =
      edgeWord fixed K x e ++ edgeWords fixed K x es := rfl

private theorem listBits_map {α β : Type} (encode : β → List Bool)
    (f : α → β) (xs : List α) :
    listBits encode (xs.map f) = listBits (fun a => encode (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons, listBits, ih]

theorem edgeFields_finRange (x : GraphReductionInput) :
    edgeFields x (List.finRange x.graph.edges.length) =
      GraphFieldMachine.fieldBits .endpoints x := by
  let encode : (Fin x.graph.n × Fin x.graph.n) → List Bool :=
    fun p => natBits p.1.val ++ natBits p.2.val
  calc
    edgeFields x (List.finRange x.graph.edges.length) =
        listBits encode ((List.finRange x.graph.edges.length).map x.graph.edges.get) := by
      exact (listBits_map encode x.graph.edges.get
        (List.finRange x.graph.edges.length)).symm
    _ = listBits encode x.graph.edges := by rw [List.map_get_finRange]
    _ = GraphFieldMachine.fieldBits .endpoints x := by
      simp only [encode, GraphFieldMachine.fieldBits, GraphFieldMachine.fieldsOutput,
        GraphReductionInput.fields, GraphInput.endpointPairs, listBits_map, pairBits]

theorem edgeWords_finRange (fixed : InventoryData) (K : Nat)
    (x : GraphReductionInput) :
    edgeWords fixed K x (List.finRange x.graph.edges.length) =
      rawRecords (jobStream (inventory fixed K x)) := by
  unfold edgeWords edgeWord
  simp only [jobStream, rawRecords, List.flatMap_assoc,
    inventory, jobDescriptors_instantiate]
  simp only [instantiate]

private theorem finRange_add_map (m start : Nat) :
    (List.finRange m).map (fun i => start + i.val) = List.range' start m := by
  induction m generalizing start with
  | zero => rfl
  | succ m ih =>
      rw [List.finRange_succ, List.map_cons, List.map_map, List.range'_succ]
      simp only [Function.comp_def, Fin.val_zero, Nat.add_zero, Fin.val_succ]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm 1] using ih (start + 1)

theorem finRange_val_map (m : Nat) :
    (List.finRange m).map Fin.val = List.range' 0 m := by
  simpa only [Nat.zero_add] using finRange_add_map m 0

theorem contiguous_finRange (m : Nat) :
    (List.finRange m).map Fin.val = List.range' 0 m :=
  finRange_val_map m

theorem contiguous_cons {m : Nat} (e : Fin m) (es : List (Fin m)) (start : Nat)
    (h : (e :: es).map Fin.val = List.range' start (e :: es).length) :
    e.val = start ∧ es.map Fin.val = List.range' (start + 1) es.length := by
  have h' : e.val :: es.map Fin.val =
      start :: List.range' (start + 1) es.length := by
    simpa only [List.map_cons, List.length_cons, List.range'_succ] using h
  exact List.cons.inj h'

end BinPackingGap.GraphPackingJobs

end

end OAI

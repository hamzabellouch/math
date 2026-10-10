import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTubes
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTiming
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPulseExpressions

namespace OAI

/-! The actual finite rational pulse compiler: ordered extraction, four
anisotropic shears in each isolated parking column, and ordered insertion. -/

noncomputable section

namespace ForcedComputation.PlanarRouting

open ShearFlows

def separationMinimum {n : ℕ} (R : Fin n → RationalBox 2) : ℚ :=
  positiveMinimum (List.ofFn fun i => positiveMinimum
    (List.ofFn fun j => if i = j then 1 else boxGap (R i) (R j)))

theorem separationMinimum_pos {n : ℕ} {R : Fin n → RationalBox 2}
    (hR : ∀ i, (R i).positive)
    (hsep : ∀ i j, i ≠ j → PositivelySeparated (R i).carrier (R j).carrier) :
    0 < separationMinimum R := by
  apply positiveMinimum_pos
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  apply positiveMinimum_pos
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  by_cases hij : i = j
  · simp [hij]
  · simpa only [hij, ite_false] using boxGap_pos_of_separated (R i) (R j) (hR i) (hR j) (hsep i j hij)

theorem separationMinimum_le {n : ℕ} (R : Fin n → RationalBox 2)
    {i j : Fin n} (hij : i ≠ j) : separationMinimum R ≤ boxGap (R i) (R j) := by
  have hr := positiveMinimum_le_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩ :
    positiveMinimum (List.ofFn fun j => if i = j then 1 else boxGap (R i) (R j)) ∈
      List.ofFn (fun k => positiveMinimum
        (List.ofFn fun j => if k = j then 1 else boxGap (R k) (R j))))
  have hc := positiveMinimum_le_of_mem (List.mem_ofFn.mpr ⟨j, by simp [hij]⟩ :
    boxGap (R i) (R j) ∈ List.ofFn fun j => if i = j then 1 else boxGap (R i) (R j))
  exact hr.trans hc

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian

def branchAt (M : Alternating.Machine) (hM : M.WellFormed)
    (i : Fin (geometricBranches M hM).length) : Branch (finiteMachine M hM) :=
  (geometricBranches M hM).get i

def branchIndex (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : Fin (geometricBranches M hM).length :=
  ⟨(geometricBranches M hM).idxOf b, List.idxOf_lt_length_of_mem
    (by simpa only [geometricBranches, List.mem_dedup] using mem_compileBranches M hM b)⟩

theorem branchAt_index (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : branchAt M hM (branchIndex M hM b) = b :=
  List.idxOf_get _

def sourceFamily (M : Alternating.Machine) (hM : M.WellFormed)
    (i : Fin (geometricBranches M hM).length) : RationalBox 2 :=
  (instruction M hM (branchAt M hM i)).source

def targetFamily (M : Alternating.Machine) (hM : M.WellFormed)
    (i : Fin (geometricBranches M hM).length) : RationalBox 2 :=
  (instruction M hM (branchAt M hM i)).target

theorem sourceFamily_separation (M : Alternating.Machine) (hM : M.WellFormed)
    (i j : Fin (geometricBranches M hM).length) (hij : i ≠ j) :
    PositivelySeparated (sourceFamily M hM i).carrier (sourceFamily M hM j).carrier := by
  apply instruction_source_separation
  intro he
  exact hij ((List.nodup_iff_injective_get.mp (List.nodup_dedup _)) he)

theorem targetFamily_separation (M : Alternating.Machine) (hM : M.WellFormed)
    (i j : Fin (geometricBranches M hM).length) (hij : i ≠ j) :
    PositivelySeparated (targetFamily M hM i).carrier (targetFamily M hM j).carrier := by
  apply instruction_target_separation
  intro he
  exact hij ((List.nodup_iff_injective_get.mp (List.nodup_dedup _)) he)

def routingCollar (M : Alternating.Machine) (hM : M.WellFormed) : ℚ :=
  min (parkingScale (geometricBranches M hM).length / 1024)
    (min (separationMinimum (sourceFamily M hM)) (separationMinimum (targetFamily M hM)) / 16)

theorem routingCollar_pos (M : Alternating.Machine) (hM : M.WellFormed) :
    0 < routingCollar M hM := by
  have hs := separationMinimum_pos (R := sourceFamily M hM)
    (fun i => instruction_source_positive M hM (branchAt M hM i)) (sourceFamily_separation M hM)
  have ht := separationMinimum_pos (R := targetFamily M hM)
    (fun i => instruction_target_positive M hM (branchAt M hM i)) (targetFamily_separation M hM)
  exact lt_min (div_pos (parkingScale_pos _) (by norm_num))
    (div_pos (lt_min hs ht) (by norm_num))

theorem routingCollar_parking_bound (M : Alternating.Machine) (hM : M.WellFormed) :
    1024 * routingCollar M hM ≤ parkingScale (geometricBranches M hM).length := by
  have h := min_le_left (parkingScale (geometricBranches M hM).length / 1024)
    (min (separationMinimum (sourceFamily M hM)) (separationMinimum (targetFamily M hM)) / 16)
  change routingCollar M hM ≤ _ at h
  linarith

theorem routingCollar_source_gap (M : Alternating.Machine) (hM : M.WellFormed)
    {i j : Fin (geometricBranches M hM).length} (hij : i ≠ j) :
    16 * routingCollar M hM ≤ boxGap (sourceFamily M hM i) (sourceFamily M hM j) := by
  have h₀ := min_le_right (parkingScale (geometricBranches M hM).length / 1024)
    (min (separationMinimum (sourceFamily M hM)) (separationMinimum (targetFamily M hM)) / 16)
  have h₁ := min_le_left (separationMinimum (sourceFamily M hM)) (separationMinimum (targetFamily M hM))
  have h₂ := separationMinimum_le (sourceFamily M hM) hij
  change routingCollar M hM ≤ _ at h₀
  linarith

theorem routingCollar_target_gap (M : Alternating.Machine) (hM : M.WellFormed)
    {i j : Fin (geometricBranches M hM).length} (hij : i ≠ j) :
    16 * routingCollar M hM ≤ boxGap (targetFamily M hM i) (targetFamily M hM j) := by
  have h₀ := min_le_right (parkingScale (geometricBranches M hM).length / 1024)
    (min (separationMinimum (sourceFamily M hM)) (separationMinimum (targetFamily M hM)) / 16)
  have h₁ := min_le_right (separationMinimum (sourceFamily M hM)) (separationMinimum (targetFamily M hM))
  have h₂ := separationMinimum_le (targetFamily M hM) hij
  change routingCollar M hM ≤ _ at h₀
  linarith

inductive Phase
  | extractHorizontal
  | extractVertical
  | scale (k : Fin 4)
  | insertVertical
  | insertHorizontal

structure Action (M : Alternating.Machine) (hM : M.WellFormed) where
  owner : Branch (finiteMachine M hM)
  phase : Phase

def actions (M : Alternating.Machine) (hM : M.WellFormed) : List (Action M hM) :=
  (sourceOrder M hM).flatMap (fun b => [⟨b, .extractHorizontal⟩, ⟨b, .extractVertical⟩]) ++
    (geometricBranches M hM).flatMap (fun b => List.ofFn fun k => ⟨b, .scale k⟩) ++
    (targetOrder M hM).flatMap (fun b => [⟨b, .insertVertical⟩, ⟨b, .insertHorizontal⟩])

def parkingFor (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : Fin 2 → ℚ :=
  parkingCenter (geometricBranches M hM).length (branchIndex M hM b)

def Action.primitive {M : Alternating.Machine} {hM : M.WellFormed} (a : Action M hM) : Primitive :=
  letI := ShearFlows.neZeroTwo
  let r := instruction M hM a.owner
  let p := parkingFor M hM a.owner
  let ε := parkingScale (geometricBranches M hM).length
  match a.phase with
  | .extractHorizontal => .translation ![p 0 - centerQ r.source 0, 0]
  | .extractVertical => .translation ![0, p 1 - centerQ r.source 1]
  | .scale 0 => .vertical p (-r.factor * (3 / 8) / ε)
  | .scale 1 => .horizontal p ((r.factor⁻¹ - 1) * ε / (3 / 8))
  | .scale 2 => .vertical p ((3 / 8) / ε)
  | .scale _ => .horizontal p ((r.factor - 1) * ε / (3 / 8))
  | .insertVertical => .translation ![0, centerQ r.target 1 - p 1]
  | .insertHorizontal => .translation ![centerQ r.target 0 - p 0, 0]

def phaseRectangle (R S : RationalBox 2) (p : Fin 2 → ℚ)
    (P : RationalBox 2) : Phase → RationalBox 2 :=
  letI := ShearFlows.neZeroTwo
  fun
  | .extractHorizontal => translationTube R (horizontalCenter R (p 0))
  | .extractVertical => translationTube (recenter R (horizontalCenter R (p 0))) p
  | .scale _ => P
  | .insertVertical => translationTube (recenter S p) (horizontalCenter S (p 0))
  | .insertHorizontal => translationTube (recenter S (horizontalCenter S (p 0))) (centerQ S)

def Action.rectangle {M : Alternating.Machine} {hM : M.WellFormed} (a : Action M hM) : RationalBox 2 :=
  let r := instruction M hM a.owner
  let p := parkingFor M hM a.owner
  phaseRectangle r.source r.target p
    (parkingBox (geometricBranches M hM).length (bandScale M) (branchIndex M hM a.owner)) a.phase

def compiledPulse (M : Alternating.Machine) (hM : M.WellFormed)
    (i : Fin (actions M hM).length) : Pulse where
  primitive := ((actions M hM).get i).primitive
  rectangle := ((actions M hM).get i).rectangle
  collar := routingCollar M hM
  start := PlanarTiming.start i
  finish := PlanarTiming.finish i

theorem compiledPulse_valid (M : Alternating.Machine) (hM : M.WellFormed)
    (i : Fin (actions M hM).length) : (compiledPulse M hM i).Valid :=
  ⟨routingCollar_pos M hM, (PlanarTiming.intervals i).2.1⟩

def compiledHamiltonian (M : Alternating.Machine) (hM : M.WellFormed) : FieldExpr :=
  processorExpression (compiledPulse M hM)

theorem compiledHamiltonian_valid (M : Alternating.Machine) (hM : M.WellFormed) :
    (compiledHamiltonian M hM).Valid := processorExpression_valid (compiledPulse_valid M hM)

theorem compiledHamiltonian_noTime (M : Alternating.Machine) (hM : M.WellFormed) :
    SpatialExpression.NoTime (compiledHamiltonian M hM) := processorExpression_noTime _

theorem compiledHamiltonian_unitPeriods (M : Alternating.Machine) (hM : M.WellFormed) :
    SpatialExpression.UnitPeriods (compiledHamiltonian M hM) := processorExpression_unitPeriods _

end ForcedComputation.Recorder.Planar

end

end OAI

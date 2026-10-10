import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.TickCarry
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.SourceAssignment
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Produced
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.SelectionCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.AssignmentRetention
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.Assignments

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryTick

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldGroupSelection AllFieldHistoryGroupedRecovery
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

abbrev Choices := ∀ sigma : Placement,
  Selected (K := K) (tick := tick) allocation m ε sigma slack

abbrev AmbientTag (sigma : Placement) :=
  JointCoarseHashing.Triple
    (AllFieldGroupOrbitData.Pos (K := K) (tick := tick) allocation m sigma)

abbrev Tags (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :=
  ∀ sigma : Placement, {e // e ∈ (chosen sigma).targets}

local instance tagsDecidableEq (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    DecidableEq (Tags allocation m ε slack chosen) := Classical.decEq _

@[instance_reducible]
private def coarseTripleFintype (P : Type) [Fintype P] :
    Fintype (JointCoarseHashing.Triple P) := inferInstance

instance ambientTagFintype (sigma : Placement) :
    Fintype (AmbientTag (K := K) (tick := tick) allocation m sigma) :=
  coarseTripleFintype (AllFieldGroupOrbitData.Pos (K := K) (tick := tick) allocation m sigma)

instance ambientTagsFintype :
    Fintype (∀ sigma, AmbientTag (K := K) (tick := tick) allocation m sigma) := inferInstance

instance tagsFintype (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype (Tags allocation m ε slack chosen) := inferInstance

def select (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (j : Tags allocation m ε slack chosen) :
    ∀ sigma, AmbientTag (K := K) (tick := tick) allocation m sigma :=
  fun sigma => AllFieldGroupOrbitData.coarse allocation m sigma (j sigma).val

theorem select_injective
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Function.Injective (select allocation m ε slack chosen) := by
  intro _ _ hequal
  funext sigma
  apply Subtype.ext
  exact AllFieldGroupOrbitData.coarse_injective allocation m sigma (congrFun hequal sigma)

def targets (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (j : Tags allocation m ε slack chosen) :
    AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m :=
  joinGroupTargets (activeCounts allocation m) (fun sigma => (j sigma).val)

def assignments (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (sigma : Placement) :=
  AllFieldGroupAssignmentRetention.physicalAssignment allocation m ε sigma
    (JointOrdinarySelection.hashLevel
      (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
    (JointOrdinarySelection.hashSet
      (selectionHashRate (K := K) (tick := tick) allocation sigma slack) m)
    (chosen sigma).sample

def assignment (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :=
  groupedAssignment allocation m (AmbientTag (K := K) (tick := tick) allocation m)
    (assignments allocation m ε slack chosen)

theorem coherent (F : Type*) [Field F]
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    JointExtraction.Coherent
      (AllFieldHistorySource.preparedSource (K := K) (tick := tick) allocation m F ε)
      (assignment allocation m ε slack chosen) := by
  apply AllFieldHistorySource.groupedAssignment_coherent allocation m F ε
  intro sigma
  exact AllFieldGroupAssignments.physicalAssignment_coherent F allocation m ε sigma
    _ _ (chosen sigma).sample

theorem repair (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack)
    (j : Tags allocation m ε slack chosen) :
    InverseLinearRecovery.RecoveredBy
      (AllFieldHistoryRecovery.ideal F allocation m ε (targets allocation m ε slack chosen j))
      (JointExtraction.branch
        (AllFieldHistorySource.preparedSource (K := K) (tick := tick) allocation m F ε)
        (assignment allocation m ε slack chosen) (select allocation m ε slack chosen j))
      (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) := by
  rw [AllFieldHistorySource.preparedSource_eq_delete]
  apply repair_grouped F allocation hε hm
    (AmbientTag (K := K) (tick := tick) allocation m)
    (assignments allocation m ε slack chosen)
    (select allocation m ε slack chosen j) (fun sigma => (j sigma).val)
  · intro sigma w hw
    have hs := AllFieldGroupAssignmentRetention.assigned_some_idealSide
      allocation m ε sigma _ _ (chosen sigma).sample (j sigma).val (sigma.symm 0, w) hw
    simpa only [Equiv.apply_symm_apply] using hs
  · intro sigma w hw
    have hs := AllFieldGroupAssignmentRetention.assigned_some_idealSide
      allocation m ε sigma _ _ (chosen sigma).sample (j sigma).val (sigma.symm 1, w) hw
    simpa only [Equiv.apply_symm_apply] using hs
  · intro sigma w hw
    have hs := AllFieldGroupAssignmentRetention.assigned_some_idealSide
      allocation m ε sigma _ _ (chosen sigma).sample (j sigma).val (sigma.symm 2, w) hw
    simpa only [Equiv.apply_symm_apply] using hs
  · intro side w hw sigma
    have hg := (chosen sigma).good (j sigma).val (j sigma).property
    have hh := AllFieldGroupAssignmentRetention.good_projected_failure_le F
      allocation m ε sigma _ _
      (JointOrdinarySelection.hashSet_AP (selectionHashRate allocation sigma slack) m)
      (m : ℝ) (chosen sigma).sample (targets allocation m ε slack chosen j)
      (by simpa only [targets, project_joinGroupTargets] using hg) side w hw
    simp only [targets, project_joinGroupTargets] at hh
    rw [filter_eq_rejected] at hh ⊢
    dsimp only [assignments, select]
    exact hh

def canonicalMap (F : Type*) [Field F]
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m) :
    LocalMap (AllFieldHistoryRecovery.ideal F allocation m ε e)
      (AllFieldHistoryRecovery.canonical (K := K) (tick := tick) F allocation m ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (AllFieldHistoryRecovery.coordinates allocation m e).symm
    (AllFieldHistoryRecovery.coordinates allocation m e).symm
    (AllFieldHistoryRecovery.coordinates allocation m e).symm _).symm.trans ?_⟩
  funext x y z
  change AllFieldHistoryRecovery.ideal F allocation m ε e _ _ _ = _
  rw [AllFieldHistoryRecovery.ideal_coordinates]
  simp only [Equiv.apply_symm_apply]

def activeExecution (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Execution
      (AllFieldHistoryRegrouping.activeTensor (K := K) (tick := tick) allocation m F ε)
      (Tensor.directSum (fun _ : Tags allocation m ε slack chosen =>
        AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε)) := by
  let prepared := (Execution.initial
    (AllFieldHistoryRegrouping.activeTensor (K := K) (tick := tick) allocation m F ε)).restrict _
      (AllFieldHistorySource.preparedMap (K := K) (tick := tick) allocation m F ε)
  let repaired := prepared.extractSelectedAndRepair
    (assignment allocation m ε slack chosen) (coherent allocation m ε slack F chosen)
    (select allocation m ε slack chosen) (select_injective allocation m ε slack chosen)
    (fun j => AllFieldHistoryRecovery.ideal F allocation m ε (targets allocation m ε slack chosen j))
    (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m)
    (repair allocation m ε slack F hε hm chosen)
  let canonical := repaired.restrict _ (LocalMap.directSum _ _
    (fun j => canonicalMap allocation m ε F (targets allocation m ε slack chosen j)))
  exact canonical.restrict _
    ((AllFieldHistoryProduced.map (K := K) (tick := tick) allocation m F hε.le).parallelCopies _)

@[simp] theorem activeExecution_copies (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype.card (activeExecution allocation m ε slack F hε hm chosen).Copies =
      2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) := by
  change Fintype.card (InverseLinearRecovery.MaskRectangles
    (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) × PUnit) = _
  rw [Fintype.card_prod, ExactRecovery.card_mask_rectangles, Fintype.card_fin,
    Fintype.card_punit, mul_one]

theorem card_tags (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype.card (Tags allocation m ε slack chosen) =
      ∏ _sigma : Placement,
        ⌊Real.exp ((m : ℝ) * (nativeCapacity (K := K) (tick := tick) allocation - slack))⌋₊ := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro sigma _
  simpa only [Fintype.card_coe] using (chosen sigma).card_targets

def execution (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Execution (stateTensor F (K := K) allocation m ε tick)
      (Tensor.directSum (fun _ : Tags allocation m ε slack chosen =>
        stateTensor F (K := K) allocation m ε (tick + 1))) :=
  AllFieldHistoryTickCarry.liftExecution (K := K) (tick := tick) allocation m F ε
    (activeExecution allocation m ε slack F hε hm chosen)

@[simp] theorem execution_copies (F : Type*) [Field F] (hε : 0 < ε)
    (hm : AllFieldHistoryRecovery.minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (chosen : Choices (K := K) (tick := tick) allocation m ε slack) :
    Fintype.card (execution allocation m ε slack F hε hm chosen).Copies =
      2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m) :=
  activeExecution_copies allocation m ε slack F hε hm chosen

end MatrixMultiplication.AllFieldHistoryTick

end

end OAI

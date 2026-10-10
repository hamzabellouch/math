import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Regrouping
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.IncomingMasks
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.RecoveryCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.GroupMasks

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistorySource

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryRegrouping AllFieldHistoryIncomingMasks
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def deleteWithPred {F : Type*} [Field F] {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (source : Tensor F X Y Z) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz] :
    LocalMap source (ExactRecovery.delete source px py pz) := by
  let d := LocalMap.delete source px py pz
  refine ⟨d.x, d.y, d.z, d.coefficient.trans ?_⟩
  funext x y z
  unfold ExactRecovery.delete
  split_ifs <;> rfl

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

abbrev Raw := AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m

def toActive (w : Raw (K := K) (tick := tick) allocation m) :
    ActiveWords (K := K) (tick := tick) allocation m := fun h => incomingWord allocation m h w

theorem parent_coefficient (F : Type*) [Field F] (h : Active K tick)
    (x y z : Raw (K := K) (tick := tick) allocation m) :
    Tensor.power
      (CWStrands.shapeTensor (Fin (currentLength h.val.1.source))
        (currentPhysicalShape (h.val.1.source, h.val.2)))
      (population allocation m (h.val.1.source, h.val.2))
      (incomingWord allocation m h x) (incomingWord allocation m h y)
      (incomingWord allocation m h z) =
    ∏ i : JointPopulation.Positions (activeCounts allocation m) h,
      AllFieldHistoryRecovery.parents F h (x h i) (y h i) (z h i) := by
  change (∏ p : Fin (population allocation m (h.val.1.source, h.val.2)),
    CWStrands.shapeTensor _ _ (incomingWord allocation m h x p)
      (incomingWord allocation m h y p) (incomingWord allocation m h z p)) = _
  refine ((sourcePositionsEquiv allocation m h).prod_comp (fun p =>
    CWStrands.shapeTensor (Fin (currentLength h.val.1.source))
      (currentPhysicalShape (h.val.1.source, h.val.2))
      (incomingWord allocation m h x p) (incomingWord allocation m h y p)
      (incomingWord allocation m h z p))).symm.trans ?_
  apply Finset.prod_congr rfl
  intro i _
  simp only [incomingWord, Equiv.symm_apply_apply]
  erw [shapeTensor_joinHalves]
  unfold AllFieldHistoryRecovery.parents JointCanonicalMixed.inputTensor
  rw [ite_eq_left rfl]
  unfold JointCanonicalCW.parentTensor currentPhysicalShape
  rw [source_shape]
  rfl

def receivedSource (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F (K := K) (tick := tick) allocation m)
    (received allocation m ε 0) (received allocation m ε 1) (received allocation m ε 2)

theorem received_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : Raw (K := K) (tick := tick) allocation m) :
    activeTensor (K := K) (tick := tick) allocation m F ε (toActive allocation m x) (toActive allocation m y)
      (toActive allocation m z) = receivedSource (K := K) (tick := tick) allocation m F ε x y z := by
  change (∏ h : Active K tick, historyTensor F allocation m ε
    (h.val.1.source, h.val.2) (incomingWord allocation m h x)
      (incomingWord allocation m h y) (incomingWord allocation m h z)) = _
  unfold receivedSource ExactRecovery.delete
  by_cases hp : received allocation m ε 0 x ∧ received allocation m ε 1 y ∧
      received allocation m ε 2 z
  · rw [ite_eq_left hp]
    change _ = ∏ h : Active K tick, ∏ i : JointPopulation.Positions (activeCounts allocation m) h,
      AllFieldHistoryRecovery.parents F h (x h i) (y h i) (z h i)
    apply Finset.prod_congr rfl
    intro h _
    unfold historyTensor ExactRecovery.delete
    rw [ite_eq_left ⟨hp.1 h, hp.2.1 h, hp.2.2 h⟩]
    exact parent_coefficient allocation m F h x y z
  · rw [ite_eq_right hp]
    have hh : ∃ h : Active K tick,
        ¬(residentMask allocation m ε (h.val.1.source, h.val.2) 0 (incomingWord allocation m h x) ∧
          residentMask allocation m ε (h.val.1.source, h.val.2) 1 (incomingWord allocation m h y) ∧
          residentMask allocation m ε (h.val.1.source, h.val.2) 2 (incomingWord allocation m h z)) := by
      by_contra hn
      apply hp
      push Not at hn
      exact ⟨fun h => (hn h).1, fun h => (hn h).2.1, fun h => (hn h).2.2⟩
    obtain ⟨h, hh⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ h)
    exact ite_eq_right hh

def receivedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (activeTensor (K := K) (tick := tick) allocation m F ε)
      (receivedSource (K := K) (tick := tick) allocation m F ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (toActive (K := K) (tick := tick) allocation m)
    (toActive (K := K) (tick := tick) allocation m)
    (toActive (K := K) (tick := tick) allocation m) _).symm.trans ?_⟩
  funext x y z
  exact received_coefficient allocation m F ε x y z

def marginal (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  JointCanonicalMixed.sideMask (activeCounts allocation m) activeHalfLength activeHalfLength
    AllFieldHistoryRecovery.halfLength_le_eight side w

def preparedSource (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  ExactRecovery.delete (receivedSource (K := K) (tick := tick) allocation m F ε)
    (fun x => marginal (K := K) (tick := tick) allocation m 0 x ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 0 x)
    (fun y => marginal (K := K) (tick := tick) allocation m 1 y ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 1 y)
    (fun z => marginal (K := K) (tick := tick) allocation m 2 z ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 2 z)

theorem preparedSource_eq_delete (F : Type*) [Field F] (ε : ℝ) :
    preparedSource (K := K) (tick := tick) allocation m F ε =
      ExactRecovery.delete (AllFieldHistoryRecovery.rawSource F (K := K) (tick := tick) allocation m)
        (AllFieldHistoryRecovery.completeKeep allocation m ε 0)
        (AllFieldHistoryRecovery.completeKeep allocation m ε 1)
        (AllFieldHistoryRecovery.completeKeep allocation m ε 2) := by
  funext x y z
  unfold preparedSource receivedSource marginal AllFieldHistoryRecovery.completeKeep
    ExactRecovery.delete
  split_ifs <;> simp_all only [and_true, true_and, not_false_eq_true]
  all_goals tauto

def preparedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (activeTensor (K := K) (tick := tick) allocation m F ε)
      (preparedSource (K := K) (tick := tick) allocation m F ε) :=
  (receivedMap (K := K) (tick := tick) allocation m F ε).comp (deleteWithPred (receivedSource (K := K) (tick := tick) allocation m F ε)
    (fun x => marginal (K := K) (tick := tick) allocation m 0 x ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 0 x)
    (fun y => marginal (K := K) (tick := tick) allocation m 1 y ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 1 y)
    (fun z => marginal (K := K) (tick := tick) allocation m 2 z ∧ AllFieldHistoryRawMasks.rawPass allocation m ε 2 z))

abbrev GroupWords := ∀ sigma : Placement,
  AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma

def groupsEquiv : Raw (K := K) (tick := tick) allocation m ≃
    GroupWords (K := K) (tick := tick) allocation m :=
  activeWordsEquivOrders (fun h : Active K tick =>
    JointPopulation.Positions (activeCounts allocation m) h →
      ((Fin (activeHalfLength h) → Fin 7) × (Fin (activeHalfLength h) → Fin 7)))

@[simp] theorem project_groups_symm
    (x : GroupWords (K := K) (tick := tick) allocation m) (sigma : Placement) :
    AllFieldHistoryGroupMasks.projectRaw allocation m sigma
      ((groupsEquiv allocation m).symm x) = x sigma :=
  congrFun ((groupsEquiv allocation m).apply_symm_apply x) sigma

theorem grouped_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : GroupWords (K := K) (tick := tick) allocation m) :
    preparedSource (K := K) (tick := tick) allocation m F ε
      ((groupsEquiv allocation m).symm x) ((groupsEquiv allocation m).symm y)
      ((groupsEquiv allocation m).symm z) =
    CommonDimensions.familyProduct
      (fun sigma => AllFieldHistoryGroupMasks.groupPreparedSource F allocation m ε sigma)
      x y z := by
  rw [preparedSource_eq_delete, AllFieldHistoryGroupMasks.preparedSource_factor]
  simp only [project_groups_symm, CommonDimensions.familyProduct]

def groupsMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (preparedSource (K := K) (tick := tick) allocation m F ε)
      (CommonDimensions.familyProduct (fun sigma : Placement =>
        AllFieldHistoryGroupMasks.groupPreparedSource F (K := K) (tick := tick)
          allocation m ε sigma)) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (groupsEquiv (K := K) (tick := tick) allocation m).symm
    (groupsEquiv (K := K) (tick := tick) allocation m).symm
    (groupsEquiv (K := K) (tick := tick) allocation m).symm _).symm.trans ?_⟩
  funext x y z
  exact grouped_coefficient allocation m F ε x y z

end MatrixMultiplication.AllFieldHistorySource

end

end OAI

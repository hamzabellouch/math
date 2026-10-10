import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.ProducedBase
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.ProducedMasks
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.RecoveryCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Regrouping

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryProduced

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryProducedMasks
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

def passes (ε : ℝ) (side : Fin 3)
    (w : AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m) : Prop :=
  ∀ h : Produced K tick, residentMask allocation m ε h.val side (w h)

theorem producedTensor_eq_delete (F : Type*) [Field F] (ε : ℝ) :
    AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε =
      ExactRecovery.delete (producedBase (F := F) (K := K) (tick := tick) allocation m)
        (passes allocation m ε 0) (passes allocation m ε 1) (passes allocation m ε 2) := by
  funext x y z
  simp only [AllFieldHistoryRegrouping.producedTensor, CommonDimensions.familyProduct,
    historyTensor, ExactRecovery.delete, Fintype.prod_ite_zero,
    passes, forall_and, producedBase]

theorem canonical_eq_delete (F : Type*) [Field F] (ε : ℝ) :
    AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε =
      ExactRecovery.delete (canonicalChildren (F := F) (K := K) (tick := tick) allocation m)
        (AllFieldHistoryMasks.childWindows allocation m ε 0)
        (AllFieldHistoryMasks.childWindows allocation m ε 1)
        (AllFieldHistoryMasks.childWindows allocation m ε 2) := by
  have hb := JointCanonicalCW.canonicalBase_eq_children (F := F)
    (activeCounts (K := K) (tick := tick) allocation m)
    activeHalfLength activeHalfLength activeParentShape
    AllFieldHistoryRecovery.halfLength_le_eight
    (fun h u hu => jointCounts_support_le allocation m h.val u hu)
  unfold AllFieldHistoryRecovery.canonical JointCanonicalization.canonicalIdeal
  change ExactRecovery.delete
    (JointCanonicalization.canonicalBase (activeCounts allocation m)
      (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength)
      (JointCanonicalCW.parentTensor activeHalfLength activeHalfLength activeParentShape)
      (JointCanonicalCW.coarse activeHalfLength activeHalfLength
        AllFieldHistoryRecovery.halfLength_le_eight))
    (AllFieldHistoryMasks.childWindows allocation m ε 0)
    (AllFieldHistoryMasks.childWindows allocation m ε 1)
    (AllFieldHistoryMasks.childWindows allocation m ε 2) = _
  rw [hb]
  rfl

def pulled (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m)
      (AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m)
      (AllFieldHistory.ProducedWords (K := K) (tick := tick) allocation m) :=
  Tensor.pullback (regroupWords allocation m) (regroupWords allocation m)
    (regroupWords allocation m)
    (AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε)

theorem delete_pulled (F : Type*) [Field F] {ε : ℝ} (hε : 0 ≤ ε) :
    ExactRecovery.delete (pulled (K := K) (tick := tick) allocation m F ε)
      (passes allocation m ε 0) (passes allocation m ε 1) (passes allocation m ε 2) =
    AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε := by
  rw [producedTensor_eq_delete]
  funext x y z
  by_cases hp : passes allocation m ε 0 x ∧ passes allocation m ε 1 y ∧
      passes allocation m ε 2 z
  · simp only [ExactRecovery.delete, ite_eq_left hp]
    unfold pulled Tensor.pullback
    rw [canonical_eq_delete]
    have hx := childWindows_of_produced_masks allocation m hε 0 x hp.1
    have hy := childWindows_of_produced_masks allocation m hε 1 y hp.2.1
    have hz := childWindows_of_produced_masks allocation m hε 2 z hp.2.2
    unfold ExactRecovery.delete
    rw [ite_eq_left ⟨hx, hy, hz⟩]
    exact regroup_coefficient allocation m x y z
  · simp only [ExactRecovery.delete, ite_eq_right hp]

def pullbackMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε)
      (pulled (K := K) (tick := tick) allocation m F ε) := by
  apply LocalMap.ofExists
  exact ⟨_, _, _, (Tensor.pullback_eq_restrict
    (regroupWords (K := K) (tick := tick) allocation m)
    (regroupWords (K := K) (tick := tick) allocation m)
    (regroupWords (K := K) (tick := tick) allocation m) _).symm⟩

def map (F : Type*) [Field F] {ε : ℝ} (hε : 0 ≤ ε) :
    LocalMap (AllFieldHistoryRecovery.canonical F (K := K) (tick := tick) allocation m ε)
      (AllFieldHistoryRegrouping.producedTensor (K := K) (tick := tick) allocation m F ε) := by
  let first := pullbackMap (K := K) (tick := tick) allocation m F ε
  let last := LocalMap.delete (pulled (K := K) (tick := tick) allocation m F ε)
    (passes allocation m ε 0) (passes allocation m ε 1) (passes allocation m ε 2)
  let combined := first.comp last
  exact ⟨combined.x, combined.y, combined.z,
    combined.coefficient.trans (delete_pulled allocation m F hε)⟩

end MatrixMultiplication.AllFieldHistoryProduced

end

end OAI

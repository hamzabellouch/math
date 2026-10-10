import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Source
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.GroupedRecovery

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistorySource

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

theorem groupedAssignment_coherent (F : Type*) [Field F] (ε : ℝ)
    (E : Placement → Type)
    (a : ∀ sigma, JointExtraction.Assignment
      (AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma)
      (AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma)
      (AllFieldHistoryGroupMasks.GroupRaw (K := K) (tick := tick) allocation m sigma) (E sigma))
    (ha : ∀ sigma, JointExtraction.Coherent
      (AllFieldHistoryGroupMasks.groupPreparedSource F allocation m ε sigma) (a sigma)) :
    JointExtraction.Coherent (preparedSource (K := K) (tick := tick) allocation m F ε)
      (AllFieldHistoryGroupedRecovery.groupedAssignment allocation m E a) := by
  intro x y z i j k hT hx hy hz
  have hprod : CommonDimensions.familyProduct
      (fun sigma => AllFieldHistoryGroupMasks.groupPreparedSource F allocation m ε sigma)
      (fun sigma => AllFieldHistoryGroupMasks.projectRaw allocation m sigma x)
      (fun sigma => AllFieldHistoryGroupMasks.projectRaw allocation m sigma y)
      (fun sigma => AllFieldHistoryGroupMasks.projectRaw allocation m sigma z) ≠ 0 := by
    rw [preparedSource_eq_delete] at hT
    exact fun hzero => hT ((AllFieldHistoryGroupMasks.preparedSource_factor
      F allocation m ε x y z).trans hzero)
  exact GroupAssignment.product_coherent _ a ha _ _ _ i j k hprod hx hy hz

end MatrixMultiplication.AllFieldHistorySource

end

end OAI

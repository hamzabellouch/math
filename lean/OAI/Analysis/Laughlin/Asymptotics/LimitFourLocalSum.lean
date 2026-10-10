import OAI.Analysis.Laughlin.FourBody.PhysicalSlaterReadout
import OAI.Analysis.Laughlin.Operators.LocalFourIndexEquiv
import OAI.Analysis.Laughlin.Operators.SymmetricPairSum

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourCopyEnd_local_sum (Q r D : ℕ) (hDQ : D ≤ Q) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
    limitFourCopyEnd Q r D x = ∑ b : LocalFourIndex D,
      (fourBodyLimitCoefficient r D D b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) •
        limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x := by
  simp only [limitFourCopyEnd,LinearMap.sum_apply]
  simp_rw [weightedFourEnd_ordered Q _ _ (fun j k => limitSliceCoefficient_antisymmetric r D _ j k hr hor)]
  have he (p : ℕ) (j k : Fin (Q+1)) :
      (if j<k then (limitSliceCoefficient r D p j.val k.val : ℂ) • limitFourEnd Q p j k x else 0) =
      (if p+j.val+k.val=D ∧ j<k then
        (fourBodyLimitCoefficient r D D p j.val k.val : ℂ) • limitFourEnd Q p j k x else 0) := by
    by_cases hjk : j<k <;> by_cases ht : p+j.val+k.val=D <;> simp [limitSliceCoefficient,hjk,ht]
  simp_rw [he]
  rw [← Fin.sum_univ_eq_sum_range]
  exact localFourIndex_sum Q D hDQ
    (fun p j k => (fourBodyLimitCoefficient r D D p j.val k.val : ℂ) • limitFourEnd Q p j k x)

end Laughlin.Fock

end OAI

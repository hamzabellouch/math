import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoKernelFresh
import OAI.Combinatorics.EditApproximation.Refinement.ComputedKernelWork

namespace OAI

namespace EditApproximation

theorem computedFamilyKernelWork_eq_fresh_sum (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N)
    (cost : ComputedFamilyMemoKey source target N → ℕ) :
    computedFamilyKernelWork source target N input cost =
      ((computedFamilyResult source target N input).freshKeys.map cost).sum :=
  rankedMemoKernelWork_eq_fresh_sum _ _ _ _ cost _ _

end EditApproximation

end OAI

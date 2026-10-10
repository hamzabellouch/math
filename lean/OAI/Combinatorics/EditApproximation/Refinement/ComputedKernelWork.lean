import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoKernelWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedLocalKernelWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter



/-- Local arithmetic annotations follow the actual memo run, hence are
incurred once per cache miss, with the original program and draw values. -/


theorem computedFamilyKernelWork_le (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N)
    (cost : ComputedFamilyMemoKey source target N → ℕ) (C : ℕ)
    (hcost : ∀ key, cost key ≤ C) :
    computedFamilyKernelWork source target N input cost ≤
      C * (computedFamilyResult source target N input).requests :=
  rankedMemoKernelWork_le _ _ _ _ cost C hcost _ _

theorem computedFamilyKernelWork_near_linear (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
      (cost : ComputedFamilyMemoKey source target N → ℕ),
      (∀ key, cost key ≤ computedLocalKernelBudget D N) →
      (computedFamilyKernelWork source target N input cost : ℝ) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedLocalKernelBudget_requests_near_linear D epsilon hepsilon] with N hN
  intro source target hsize input cost hcost
  have h := computedFamilyKernelWork_le source target N input cost
    (computedLocalKernelBudget D N) hcost
  have hr : (computedFamilyKernelWork source target N input cost : ℝ) ≤
      (computedLocalKernelBudget D N : ℝ) * (computedFamilyResult source target N input).requests := by
    exact_mod_cast h
  exact hr.trans (by simpa only [mul_comm] using hN source target hsize input)

end EditApproximation

end OAI

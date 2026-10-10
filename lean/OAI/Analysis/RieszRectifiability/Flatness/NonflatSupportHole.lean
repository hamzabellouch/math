import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.UniformNonflatLimits
import OAI.Analysis.RieszRectifiability.Flatness.FullPlaneDimension

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem directedBallDeviation_self {d : ℕ} (S : Set (Ambient d)) (a : Ambient d) (r : ℝ) :
    directedBallDeviation S S a r = 0 := by
  apply le_antisymm _ (directedBallDeviation_nonneg S S a r)
  exact directedBallDeviation_le S S a r 0 le_rfl
    (fun _ _ hx => (infDist_zero_of_mem hx).le)

theorem bilateralBeta_zero_of_plane_support {n d : ℕ} (μ : Measure (Ambient d))
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hsupport : μ.support = (S : Set (Ambient d))) (a : Ambient d)
    (r : ℝ) (hr : 0 ≤ r) : bilateralBeta n μ a r = 0 := by
  apply le_antisymm _ (bilateralBeta_nonneg n μ a r hr)
  apply (bilateralBeta_le_planeError n μ a r hr S hS).trans
  simp only [bilateralPlaneError, hsupport, directedBallDeviation_self, add_zero, zero_div, le_refl]

theorem GlobalBilateralLower.exists_relative_hole {n d : ℕ}
    (μ : Measure (Ambient d)) (C G ε : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hε : 0 < ε) (hbad : GlobalBilateralLower n μ ε)
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d))) :
    ∃ c : Ambient d, c ∈ P ∧ c ∉ μ.support := by
  by_contra hnone
  have hfull : μ.support = (P : Set (Ambient d)) := by
    apply Set.Subset.antisymm hP
    intro x hx
    by_contra hxs
    exact hnone ⟨x, hx, hxs⟩
  have hdim := full_support_submodule_finrank_eq μ C G hC hg hlower P hfull
  have hS : IsAffineNPlane n P.toAffineSubspace := by
    refine ⟨⟨0, P.zero_mem⟩, ?_⟩
    rw [Submodule.toAffineSubspace_direction, hdim]
  have hzero : (0 : Ambient d) ∈ μ.support := by rw [hfull]; exact P.zero_mem
  have hb := hbad 0 hzero 1 zero_lt_one
  rw [bilateralBeta_zero_of_plane_support μ P.toAffineSubspace hS hfull 0 1 zero_le_one] at hb
  exact (not_le_of_gt hε) hb

end

end RieszRectifiability

end OAI

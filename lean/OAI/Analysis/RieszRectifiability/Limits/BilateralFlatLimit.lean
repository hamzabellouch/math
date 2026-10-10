import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BilateralBeta
import OAI.Analysis.RieszRectifiability.Limits.BilateralSupportConvergence

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem isAffineNPlane_isometric_range {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    IsAffineNPlane n L.toLinearMap.range.toAffineSubspace := by
  refine ⟨⟨0, L.toLinearMap.range.zero_mem⟩, ?_⟩
  rw [Submodule.toAffineSubspace_direction, LinearMap.finrank_range_of_inj L.injective]
  exact finrank_euclideanSpace_fin

theorem compactTestConvergence_bilateralBeta_tendsto_zero {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hsupport : ν.support = (S : Set (Ambient d))) (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun j => bilateralBeta n (μ j) a r) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro t ht
    exact Eventually.of_forall fun j => ht.trans_le (bilateralBeta_nonneg n (μ j) a r hr.le)
  · intro ε hε
    filter_upwards [compactTestConvergence_bilateral_support_tubes n μ ν hlocal C hC
      hlower hdiam a r (ε * r / 4) (by positivity)] with j hj
    exact bilateralBeta_lt_of_support_tubes n (μ j) a r ε hr hε S hS
      (by simpa only [hsupport] using! hj.1) (by simpa only [hsupport] using! hj.2)

end

end RieszRectifiability

end OAI

import OAI.Geometry.RCD.Sobolev.PoissonHarmonicCompactnessInput
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! # Fixed metric bounds for the interior smooth test class -/

open Set Metric
open scoped NNReal ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem InteriorSmoothTest.metric_bounds {n : ℕ} {S : ℝ} (hS : 0<S)
    {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ<S ∧ ∃ M B : ℝ≥0, LipschitzWith M ψ ∧
      (∀ z, |ψ z|≤B) ∧ ∀ z, ρ≤‖z‖ → ψ z=0 := by
  obtain ⟨ρ,hρ,hsub⟩ := exists_pos_lt_subset_ball hS (isClosed_tsupport ψ) hψ.2.2
  obtain ⟨M,hM⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψ.2.1 hψ.1 (by simp)
  obtain ⟨A,hA⟩ := hψ.2.1.exists_bound_of_continuous hψ.1.continuous
  let B : ℝ≥0 := ⟨max A 0,le_max_right _ _⟩
  refine ⟨ρ,hρ.1,hρ.2,M,B,hM,?_,?_⟩
  · intro z
    have hb : |ψ z|≤A := by simpa only [Real.norm_eq_abs] using hA z
    exact hb.trans (le_max_left _ _)
  · intro z hz
    by_contra hne
    have hm : ‖z‖<ρ := by
      simpa only [mem_ball,dist_zero_right] using hsub (subset_tsupport ψ hne)
    exact (not_lt_of_ge hz) hm

end RegularPointCoordinates

end

end OAI

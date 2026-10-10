import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.HeightPairingRegions

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem limiting_height_equation_of_local_limits {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (a : Ambient d) (s : ℕ → Set (Ambient d))
    (w φ : ℕ → Ambient d → ℝ) (f ψ : Ambient d → ℝ)
    (hlocal : ∀ H, Tendsto
      (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) (φ j) q.1 q.2
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear m f ψ q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H)))))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hsmall : ∀ᶠ H in atTop, ∀ᶠ j in atTop,
      |heightPairingOn m (μ j) a (s H) (w j) (φ j)| ≤ error j)
    (htail : ∀ ε : ℝ, 0 < ε → ∀ᶠ H in atTop, ∀ᶠ j in atTop,
      (∫ q, |renormalizedNormalIntegrand m (w j) (φ j) a q|
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)ᶜ)) < ε) :
    Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear m f ψ q.1 q.2 ∂(ν.restrict (s H)).prod (ν.restrict (s H))))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have htail' := htail (ε / 3) hthird
  have herror' := herror.eventually (gt_mem_nhds hthird)
  have hfinal : ∀ᶠ H in atTop,
      dist ((1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m f ψ q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H)))) 0 < ε := by
    filter_upwards [hsmall, htail'] with H hHsmall hHtail
    have hlim : Tendsto (fun j => |(1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
        fractionalBilinear m (w j) (φ j) q.1 q.2
          ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)))|) atTop
        (𝓝 (|(1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m f ψ q.1 q.2
          ∂(ν.restrict (s H)).prod (ν.restrict (s H)))|)) := by
      simpa only [Real.norm_eq_abs] using! ((hlocal H).const_mul (1 / 2 : ℝ)).norm
    have hbound : ∀ᶠ j in atTop, |(1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
        fractionalBilinear m (w j) (φ j) q.1 q.2
          ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)))| ≤ 2 * ε / 3 := by
      filter_upwards [hHsmall, hHtail, herror'] with j hj hjtail hjerror
      let I := (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
        fractionalBilinear m (w j) (φ j) q.1 q.2
          ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)))
      let F := ∫ q, renormalizedNormalIntegrand m (w j) (φ j) a q
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)ᶜ)
      have hF : |F| < ε / 3 := by
        apply lt_of_le_of_lt _ hjtail
        simpa only [Real.norm_eq_abs] using! norm_integral_le_integral_norm
          (renormalizedNormalIntegrand m (w j) (φ j) a)
      change |I + F| ≤ error j at hj
      have hI : |I| ≤ |I + F| + |F| := by
        have h := abs_add_le (I + F) (-F)
        rw [show I + F + -F = I by ring, abs_neg] at h
        exact h
      change |I| ≤ 2 * ε / 3
      linarith
    have hlimit := le_of_tendsto hlim hbound
    rw [Real.dist_eq, sub_zero]
    linarith
  exact eventually_atTop.mp hfinal

end

end RieszRectifiability

end OAI

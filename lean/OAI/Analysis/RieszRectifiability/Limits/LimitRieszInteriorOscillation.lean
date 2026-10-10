import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.OscillationTests
import OAI.Analysis.RieszRectifiability.Limits.CompactRieszInteriorLimit
import OAI.Analysis.RieszRectifiability.Limits.CompactRieszPairingTail

namespace OAI

/-!
# Interior bounds from vanishing Riesz oscillation

Mean-corrected compactly supported tests transfer scalar oscillation estimates along
a compact-test convergent sequence of measures. As the oscillation tends to zero on
expanding balls, convergence of the interior pairing leaves only the quantitative
tail bound for the limit measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem limit_rieszInterior_bound_of_oscillation {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, SFinite (μ j)]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν)
    (a : Ambient d) (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (v j))
    (e : Ambient d) (he : ‖e‖ ≤ 1)
    (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsφ : ∀ x, φ x ≠ 0 → dist x a ≤ H) (hsη : ∀ x, η x ≠ 0 → dist x a ≤ H)
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0) :
    |(1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R)))| ≤
      compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R := by
  let (j : ℕ) := (hg j).finite_on_compacts
  let ξ := fun j => meanCorrection (μ j) φ η
  have hadm := (compact_meanCorrection_admissible μ ν hweak φ η Lφ Lη Bφ Bη
    hφ hη hcφ hcη hBφ hBη hmean hbump).2
  have hsξ : ∀ j x, ξ j x ≠ 0 → dist x a ≤ H := by
    intro j x hx
    by_contra hn
    have hzφ : φ x = 0 := by by_contra hne; exact hn (hsφ x hne)
    have hzη : η x = 0 := by by_contra hne; exact hn (hsη x hne)
    exact hx (by simp only [ξ, meanCorrection, hzφ, hzη, mul_zero, sub_zero])
  have hIlim := (compactTestConvergence_corrected_rieszInterior_ball p C D μ ν hg hgν
    hweak a R hR hboundary hmass e φ η Lφ Lη Bφ Bη hφ hη hcφ hcη hBφ hBη hmean hbump).const_mul
      (1 / 2 : ℝ)
  let err := fun j => (((Lφ + Lη : ℝ≥0) : ℝ) + 1) * v j
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [mul_zero] using! hv.const_mul (((Lφ + Lη : ℝ≥0) : ℝ) + 1)
  have hbound : ∀ᶠ j in atTop,
      |(1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e (ξ j) q
        ∂((μ j).restrict (ball a R)).prod ((μ j).restrict (ball a R)))| ≤
        err j + compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R := by
    filter_upwards [hadm, hA.eventually (eventually_gt_atTop H)] with j hj hjA
    have hp := oscillation_bound_for_localized_test p C (μ j) (hg j) a (A j) (v j)
      (hH.trans_lt hjA) (hosc j) e he (ξ j) (Lφ + Lη) hj.2.2.2.1 H R hH hR hHR hjA
      (hsξ j) hj.2.2.1
    have ht := rieszScalarPairing_interior_tail_bound (p + 1) C (μ j) (hg j) a H R hH hR hHR
      e (ξ j) (Lφ + Lη) (Bφ + Bη) hj.2.2.2.1 hj.2.2.2.2.1 (hsξ j)
    let P := rieszScalarPairing (p + 1) (μ j) a R e (ξ j)
    let I := (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e (ξ j) q
      ∂((μ j).restrict (ball a R)).prod ((μ j).restrict (ball a R)))
    have htri : |I| ≤ |P| + |P - I| := by
      have h := abs_add_le P (-(P - I))
      rw [show P + -(P - I) = I by ring, abs_neg] at h
      exact h
    exact htri.trans (add_le_add hp ht)
  have hright : Tendsto
      (fun j => err j + compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R) atTop
      (𝓝 (compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R)) := by
    simpa only [zero_add] using! herr.add_const (compactRieszTailConstant (p + 1) C e H (Bφ + Bη) / R)
  exact le_of_tendsto_of_tendsto hIlim.abs hright hbound

end

end RieszRectifiability

end OAI

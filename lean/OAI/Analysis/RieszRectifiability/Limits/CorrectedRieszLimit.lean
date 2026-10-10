import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CorrectedLocalLimits
import OAI.Analysis.RieszRectifiability.Kernel.LocalTestMoments
import OAI.Analysis.RieszRectifiability.Kernel.RegionOscillation
import OAI.Analysis.RieszRectifiability.Kernel.RegionTailDecay
import OAI.Analysis.RieszRectifiability.Limits.LimitingHeightEquation

namespace OAI

/-!
# Corrected Riesz limiting equation

Mean-corrected compact tests connect the local bilinear limits to the Riesz
oscillation estimates. Together with the normalized height tail bounds, this
shows that the limiting fractional pairing vanishes along the region exhaustion.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem corrected_riesz_limiting_equation {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, SFinite (μ j)] [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hweak : CompactTestConvergence μ ν)
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hCB : C * 2 ^ (p + 1) ≤ B)
    (a : Ambient d) (s : ℕ → Set (Ambient d)) (hs : ∀ H, MeasurableSet (s H))
    (hcontain : ∀ r : ℝ, ∀ᶠ H in atTop, ball a r ⊆ s H)
    (H₀ R : ℝ) (hH₀ : 0 ≤ H₀) (hR : 0 < R) (hHR : 2 * H₀ ≤ R)
    (T : ℕ → ℝ) (hRT : ∀ H, R ≤ T H) (hout : ∀ H, s H ⊆ ball a (T H))
    (u : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (e : ℕ → Ambient d) (he : ∀ j, ‖e j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (e j) (x - y))
    (δ A v : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (v j))
    (hratio : Tendsto (fun j => v j / δ j) atTop (𝓝 0))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (b W : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : ∀ j, |u j a| ≤ W)
    (hlast : Tendsto (fun j => (R * (2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsecond : ∀ j k, k < N j → (∫ y in dyadicAnnulus a R k, u j y ^ 2 ∂μ j) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ j * (R * 2 ^ k) * b ^ k) ^ 2)
    (M : ℝ) (hM : 0 ≤ M)
    (hmass : ∀ j, ((μ j).restrict (ball a R)).real univ ≤ M)
    (hL2 : ∀ j, MemLp (fun x => u j x / δ j) 2 ((μ j).restrict (ball a R)))
    (hsecondLocal : ∀ j, (∫ x in ball a R, (u j x / δ j) ^ 2 ∂μ j) ≤ M)
    (hwI : ∀ H j, Integrable (fun x => u j x / δ j) ((μ j).restrict (s H)))
    (henergy : ∀ H j, Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
      (((μ j).restrict (s H)).prod ((μ j).restrict (s H))))
    (f φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (hφsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H₀)
    (hηsupport : ∀ x, η x ≠ 0 → dist x a ≤ H₀)
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0)
    (hlimitφ : ∀ H, Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (fun x => u j x / δ j) φ q.1 q.2
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f φ q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H)))))
    (hlimitη : ∀ H, Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (fun x => u j x / δ j) η q.1 q.2
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f η q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H))))) :
    Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) f φ q.1 q.2 ∂(ν.restrict (s H)).prod (ν.restrict (s H))))
      atTop (𝓝 0) := by
  let ξ := fun j => meanCorrection (μ j) φ η
  let w := fun j x => u j x / δ j
  let (j : ℕ) : IsFiniteMeasure ((μ j).restrict (ball a R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C (μ j) (hg j) a R hR
  let (H j : ℕ) : IsFiniteMeasure ((μ j).restrict (s H)) := ⟨by
    have hi := (isCompact_closedBall a (T H)).measure_lt_top (μ := μ j)
    simpa only [Measure.restrict_apply_univ] using!
      (measure_mono ((hout H).trans ball_subset_closedBall)).trans_lt hi⟩
  obtain ⟨hc, hadmissible⟩ := compact_meanCorrection_admissible μ ν hweak φ η Lφ Lη Bφ Bη
    hφ hη hcφ hcη hBφ hBη hmean hbump
  have hξcont : ∀ j, Continuous (ξ j) :=
    fun j => (meanCorrection_lipschitz (μ j) hφ hη).continuous
  have hξI : ∀ j, Integrable (ξ j) (μ j) := fun j => meanCorrection_integrable (μ j) φ η
    (hφ.continuous.integrable_of_hasCompactSupport hcφ)
    (hη.continuous.integrable_of_hasCompactSupport hcη)
  have hξnear : ∀ j x, ξ j x ≠ 0 → dist x a ≤ H₀ := by
    intro j x hx
    by_contra h
    have hφx : φ x = 0 := by by_contra hn; exact h (hφsupport x hn)
    have hηx : η x = 0 := by by_contra hn; exact h (hηsupport x hn)
    exact hx (by simp only [ξ, meanCorrection, hφx, hηx, mul_zero, sub_zero])
  have hξzero : ∀ j x, x ∉ ball a R → ξ j x = 0 := by
    intro j x hx
    by_contra hn
    exact hx ((hξnear j x hn).trans_lt (by linarith : H₀ < R))
  have hξu : ∀ j, Integrable (fun x => ξ j x * u j x) (μ j) := fun j =>
    meanCorrection_height_product_integrable (μ j) φ η (u j)
      hφ.continuous hη.continuous (hu j).continuous hcφ hcη
  have hξw : ∀ j, Integrable (fun x => ξ j x * w j x) (μ j) := fun j =>
    meanCorrection_height_product_integrable (μ j) φ η (w j)
      hφ.continuous hη.continuous ((hu j).continuous.div_const (δ j)) hcφ hcη
  let P := ((Bφ + Bη : ℝ≥0) : ℝ) * M
  have hmoments : ∀ᶠ j in atTop,
      (∫ x in ball a R, |ξ j x| ∂μ j) ≤ P ∧
      (∫ x in ball a R, |ξ j x * w j x| ∂μ j) ≤ P := by
    filter_upwards [hadmissible] with j hj
    exact (bounded_test_local_moment_bounds ((μ j).restrict (ball a R)) (w j) (ξ j) (hL2 j)
      (hξcont j).measurable (Bφ + Bη) hj.2.2.2.2.1 M hM (hmass j) (hsecondLocal j)).2.2
  have htail := normalized_region_tails_vanish (p + 1) C B μ (ball a R) measurableSet_ball
    s a hcontain hg hCB u ξ K hu (fun j => (hξcont j).measurable) (fun j => (hξI j).restrict)
    hξzero H₀ R hH₀ hR hHR subset_rfl (fun j => Eventually.of_forall (hξnear j))
    N hN δ hδ b W P hb0 hb2 hW (fun j => (hξw j).restrict)
    (hmoments.mono fun _ h => h.1) (hmoments.mono fun _ h => h.2) hlast hsecond
  have hcorrectedLimits : ∀ H, Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (w j) (ξ j) q.1 q.2
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f φ q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H)))) := by
    intro H
    apply globally_corrected_local_singular_limit (p + 1) μ (s H) w φ η hc
    · intro j
      exact (fractional_bilinear_integrable_and_cap_error p C ((μ j).restrict (s H))
        (globalGrowth_restrict (p + 1) C (μ j) (hg j) (s H)) (w j) φ
        ((hu j).continuous.div_const (δ j)).measurable (hwI H j) Lφ Bφ hφ hBφ
        (henergy H j) 1 (by norm_num)).1
    · intro j
      exact (fractional_bilinear_integrable_and_cap_error p C ((μ j).restrict (s H))
        (globalGrowth_restrict (p + 1) C (μ j) (hg j) (s H)) (w j) η
        ((hu j).continuous.div_const (δ j)).measurable (hwI H j) Lη Bη hη hBη
        (henergy H j) 1 (by norm_num)).1
    · exact hlimitφ H
    · exact hlimitη H
  let error := fun j => (((Lφ + Lη : ℝ≥0) : ℝ) + 1) * (v j / δ j)
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [mul_zero] using! hratio.const_mul (((Lφ + Lη : ℝ≥0) : ℝ) + 1)
  have hsmall : ∀ᶠ H in atTop, ∀ᶠ j in atTop,
      |heightPairingOn (p + 1) (μ j) a (s H) (w j) (ξ j)| ≤ error j := by
    filter_upwards [hcontain R] with H hH
    filter_upwards [hadmissible, hA.eventually (eventually_gt_atTop H₀)] with j hj hjA
    have hfar := region_far_integrable_of_lipschitz_height (p + 1) C (μ j) (hg j)
      (ball a R) (s H) measurableSet_ball a H₀ R hH₀ hR hHR subset_rfl hH
      (u j) (ξ j) K (hu j) (hξcont j).measurable (hξI j).restrict (hξu j).restrict
      (hξzero j) (hξnear j)
    exact normalized_region_pairing_oscillation_bound p C (μ j) (hg j) (e j) (he j)
      (u j) (ξ j) K (Lφ + Lη) (hu j) hj.2.2.2.1 (hdiff j) a H₀ R (T H) (A j) (v j) (δ j)
      hH₀ hR hHR (hRT H) hjA (hδ j) (hosc j) (s H) (hs H) hH (hout H)
      (hξI j) hj.2.2.1 (hξnear j) hfar
  exact limiting_height_equation_of_local_limits (p + 1) μ ν a s w ξ f φ hcorrectedLimits
    error herror hsmall (fun ε hε => (htail ε hε).mono fun _ h => h.mono fun _ hj => hj.2)

end

end RieszRectifiability

end OAI

import OAI.Geometry.RCD.Sobolev.HarmonicGradientInput
import OAI.Geometry.RCD.Sobolev.WeakRadialCancellation

namespace OAI

/-! # Interior gradient control from the harmonic radial correction -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem localGamma_add_self_le (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (f g : SobolevSpace μ hQ) :
    ∀ᵐ x ∂μ, localGamma μ hQ (f + g) (f + g) x ≤
      2 * localGamma μ hQ f f x + 2 * localGamma μ hQ g g x := by
  filter_upwards [localGamma_add_left μ hQ f g (f + g),
    localGamma_add_right μ hQ f f g, localGamma_add_right μ hQ g f g,
    localGamma_comm μ hQ f g, localGamma_self μ hQ f, localGamma_self μ hQ g,
    localGamma_abs_le μ hQ f g] with x hl hr hs hc hf hg hb
  rw [hl, hr, hs, ← hc, hf, hg]
  have hu := (le_abs_self (localGamma μ hQ f g x)).trans hb
  nlinarith [sq_nonneg (SobolevSpace.minimalSlope μ hQ f x - SobolevSpace.minimalSlope μ hQ g x)]

omit [BorelSpace X] [ProperSpace X] in
theorem sobolev_restrict_norm_sq (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (s : Set X) (f : SobolevSpace μ hQ) :
    ‖SobolevSpace.restrictLp μ hQ s f‖ ^ 2 =
      ∫ x in s, (SobolevSpace.toLp μ hQ f x) ^ 2 ∂μ := by
  rw [l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [SobolevSpace.restrictLp_coe μ hQ s f] with x hx
  rw [hx]

/-- The harmonic part is controlled by the interior gradient
estimate; the zero-boundary correction retains its full energy budget.
This supplies the radial W12 step without assuming bounded harmonic data. -/
theorem correction_interior_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hgradient : LocalHarmonicL2GradientInput hX)
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (g h F : SobolevSpace (hausdorff n X) hX.quadratic),
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) h →
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) F →
      ∀ {D I J : ℝ},
      energyForm (hausdorff n X) hX.quadratic (g - h) (g - h) ≤ D →
      ‖SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) (g - F)‖ ^ 2 ≤ I →
      ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic (g - h)‖ ^ 2 ≤ J →
      (∫ x in ball p (R / 2), localGamma (hausdorff n X) hX.quadratic (g - F) (g - F) x
        ∂hausdorff n X) ≤ 2 * D + 4 * (C / R) ^ 2 * (I + J) := by
  obtain ⟨C, hC, hpoint⟩ := hgradient hn κ (1 / 2) hκ (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv g h F hh hF D I J hD hI hJ
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hhF : IsSobolevHarmonicOn μ hQ (ball p R) (h - F) := by
    simpa only [neg_one_smul, ← sub_eq_add_neg] using hh.add μ hQ (hF.smul μ hQ (-1))
  have hlocalJ : ‖SobolevSpace.restrictLp μ hQ (ball p R) (g - h)‖ ^ 2 ≤ J := by
    rw [sobolev_restrict_norm_sq]
    apply le_trans (setIntegral_le_integral (Lp.memLp
      (SobolevSpace.toLp μ hQ (g - h))).integrable_sq (Filter.Eventually.of_forall fun _ => sq_nonneg _))
    rwa [lp_integral_square_eq_norm_square]
  have hnorm : ‖SobolevSpace.restrictLp μ hQ (ball p R) (h - F)‖ ^ 2 ≤ 2 * (I + J) := by
    have he : h - F = (g - F) - (g - h) := by abel
    rw [he, map_sub]
    have ht := norm_sub_le (SobolevSpace.restrictLp μ hQ (ball p R) (g - F))
      (SobolevSpace.restrictLp μ hQ (ball p R) (g - h))
    have ht2 := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ht
    nlinarith [sq_nonneg (‖SobolevSpace.restrictLp μ hQ (ball p R) (g - F)‖ -
      ‖SobolevSpace.restrictLp μ hQ (ball p R) (g - h)‖)]
  have hmass : 0 < μ.real (ball p R) := ENNReal.toReal_pos
    (ne_of_gt (hX.fullSupport p R hR)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  have hmean : ∫ x in ball p R, (SobolevSpace.toLp μ hQ (h - F) x) ^ 2 ∂μ ≤ 2 * (I + J) := by
    rwa [sobolev_restrict_norm_sq] at hnorm
  have hgrad : ∀ᵐ x ∂μ.restrict (ball p (R / 2)), localGamma μ hQ (h - F) (h - F) x ≤
      (C / R) ^ 2 * ((μ.real (ball p R))⁻¹ * (2 * (I + J))) := by
    have hp := hpoint p R hR hcurv (h - F) hhF
    have he : (1 / 2 : ℝ) * R = R / 2 := by ring
    rw [he] at hp
    filter_upwards [hp] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmean
      (inv_nonneg.mpr hmass.le)) (sq_nonneg _))
  have henergyH : (∫ x in ball p (R / 2), localGamma μ hQ (h - F) (h - F) x ∂μ) ≤
      2 * (C / R) ^ 2 * (I + J) := by
    let : IsFiniteMeasure (μ.restrict (ball p (R / 2))) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded (ball p (R / 2)) isBounded_ball⟩
    have hi := integral_mono_ae (localGamma_memL1 μ hQ (h - F) (h - F)).integrableOn
      (integrable_const ((C / R) ^ 2 * ((μ.real (ball p R))⁻¹ * (2 * (I + J))))) hgrad
    have hIJ : 0 ≤ I + J := by
      linarith [sq_nonneg (‖SobolevSpace.restrictLp μ hQ (ball p R) (g - F)‖),
        sq_nonneg (‖SobolevSpace.toLp μ hQ (g - h)‖)]
    simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at hi
    have hv := measureReal_mono (ball_subset_ball (show R / 2 ≤ R by linarith))
      (ne_of_lt (hX.finiteOnBounded (ball p R) isBounded_ball))
    apply hi.trans
    calc
      _ ≤ μ.real (ball p R) * ((C / R) ^ 2 * ((μ.real (ball p R))⁻¹ * (2 * (I + J)))) :=
        mul_le_mul_of_nonneg_right hv (by positivity)
      _ = _ := by field_simp
  have henergyG : (∫ x in ball p (R / 2), localGamma μ hQ (g - h) (g - h) x ∂μ) ≤ D := by
    have hn : ∀ᵐ x ∂μ, 0 ≤ localGamma μ hQ (g - h) (g - h) x := by
      filter_upwards [localGamma_self μ hQ (g - h)] with x hx
      rw [hx]; positivity
    apply le_trans (setIntegral_le_integral (localGamma_memL1 μ hQ (g - h) (g - h)) hn)
    rwa [integral_localGamma_eq_energyForm]
  have he : g - F = (g - h) + (h - F) := by abel
  have hb := integral_mono_ae (μ := μ.restrict (ball p (R / 2)))
    (localGamma_memL1 μ hQ (g - F) (g - F)).integrableOn
    (((localGamma_memL1 μ hQ (g - h) (g - h)).integrableOn.const_mul 2).add
      ((localGamma_memL1 μ hQ (h - F) (h - F)).integrableOn.const_mul 2))
    (ae_restrict_of_ae (by simpa only [he, Pi.add_apply] using localGamma_add_self_le μ hQ (g - h) (h - F)))
  simp only [Pi.add_apply] at hb
  rw [integral_add ((localGamma_memL1 μ hQ (g - h) (g - h)).integrableOn.const_mul 2)
    ((localGamma_memL1 μ hQ (h - F) (h - F)).integrableOn.const_mul 2)] at hb
  simp only [integral_const_mul] at hb
  linarith

end RegularPointCoordinates

end

end OAI

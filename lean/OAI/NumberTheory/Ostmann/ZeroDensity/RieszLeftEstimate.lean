import OAI.NumberTheory.Ostmann.ZeroDensity.RieszTailEstimate

namespace OAI

/-! # The bounded left vertical segment of the Riesz contour -/

namespace Ostmann

open Complex MeasureTheory Set

noncomputable def rieszLineMajorant (t : ℝ) : ℝ := 9 * (1 + |t|) ^ (-(2 : ℝ))

theorem rieszLineMajorant_nonneg (t : ℝ) : 0 ≤ rieszLineMajorant t := by
  unfold rieszLineMajorant
  positivity

theorem rieszLineMajorant_integrable : Integrable rieszLineMajorant := by
  have hp : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (μ := volume) (E := ℝ)
      (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)
  change Integrable (fun t : ℝ => 9 * (1 + |t|) ^ (-(2 : ℝ)))
  simpa only [Real.norm_eq_abs] using hp.const_mul 9

theorem rieszMellinKernel_half_strip (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖rieszMellinKernel s‖ ≤ rieszLineMajorant s.im := by
  have h1 : 1 ≤ 2 * ‖s‖ := by linarith [Complex.re_le_norm s]
  have h2 : 1 ≤ 2 * ‖s + 1‖ := by
    have hh := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at hh
    linarith
  have hsp : 0 < ‖s‖ := by linarith
  have hsp1 : 0 < ‖s + 1‖ := by linarith
  have ht1 := Complex.abs_im_le_norm s
  have ht2 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
  have ha : 0 < 1 + |s.im| := by positivity
  have hp : (1 + |s.im|) ^ 2 ≤ 9 * (‖s‖ * ‖s + 1‖) := by
    have hh := mul_le_mul (show 1 + |s.im| ≤ 3 * ‖s‖ by linarith)
      (show 1 + |s.im| ≤ 3 * ‖s + 1‖ by linarith) (by positivity) (by positivity)
    nlinarith
  rw [rieszMellinKernel, norm_div, norm_one, norm_mul, rieszLineMajorant,
    Real.rpow_neg (by positivity : 0 ≤ 1 + |s.im|), Real.rpow_two, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖s‖ * ‖s + 1‖) (sq_pos_of_pos ha)).mpr
  nlinarith

theorem leftRieszIntegrand_segment_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (χ : PrimitiveComplexCharacter) (X a T M : ℝ), 0 < X → 1 / 2 ≤ a → 0 ≤ M →
      (∀ t ∈ Icc (-T) T, ‖logDeriv χ.L (rieszMellinLine a t)‖ ≤ M) →
      ‖∫ t in Icc (-T) T, rightRieszIntegrand χ X a t‖ ≤ K * M * X ^ a := by
  let J := ∫ t : ℝ, rieszLineMajorant t
  have hJ : 0 ≤ J := integral_nonneg rieszLineMajorant_nonneg
  refine ⟨J + 1, by linarith, ?_⟩
  intro χ X a T M hX ha hM hb
  have hg : Integrable (fun t : ℝ => (M * X ^ a) * rieszLineMajorant t) :=
    rieszLineMajorant_integrable.const_mul _
  have hnorm : ‖∫ t in Icc (-T) T, rightRieszIntegrand χ X a t‖ ≤
      ∫ t in Icc (-T) T, (M * X ^ a) * rieszLineMajorant t := by
    apply norm_integral_le_of_norm_le hg.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hk := rieszMellinKernel_half_strip (rieszMellinLine a t) (by simpa using ha)
    simp only [rieszMellinLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add] at hk
    rw [rightRieszIntegrand, norm_mul, norm_neg, rieszVerticalWeight_norm X a t hX]
    have hh := mul_le_mul (hb t ht) (mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hX.le a))
      (by positivity) hM
    exact hh.trans_eq (by ring)
  have hfull := setIntegral_le_integral hg
    (Filter.Eventually.of_forall (fun t => mul_nonneg (by positivity) (rieszLineMajorant_nonneg t)))
    (s := Icc (-T) T)
  simp only [integral_const_mul] at hnorm hfull
  apply (hnorm.trans hfull).trans
  dsimp only [J] at hJ ⊢
  nlinarith [mul_nonneg hM (Real.rpow_nonneg hX.le a)]

end Ostmann

end OAI

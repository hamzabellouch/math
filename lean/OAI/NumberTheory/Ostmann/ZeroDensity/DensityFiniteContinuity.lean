import OAI.NumberTheory.Ostmann.ZeroDensity.DensityKernelCost

namespace OAI

/-! # Continuity of the actual finite square on a bounded height interval -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators

 theorem densitySquareKernel_vertical_continuous (χ : PrimitiveComplexCharacter)
    (c : ℝ) (hc : 0 < c) :
    Continuous (fun z : ℝ × ℝ => densitySquareKernel χ
      (densityVerticalPoint (1 / 2) z.1) ((c : ℂ) + (2 * Real.pi * z.2 : ℝ) * I)) := by
  have hs : Continuous (fun z : ℝ × ℝ => densityVerticalPoint (1 / 2) z.1) := by
    unfold densityVerticalPoint
    fun_prop
  have hw : Continuous (fun z : ℝ × ℝ => (c : ℂ) + (2 * Real.pi * z.2 : ℝ) * I) := by fun_prop
  have hg : Continuous (fun z : ℝ × ℝ => DirichletCharacter.gammaFactor χ.character
      (densityVerticalPoint (1 / 2) z.1 + ((c : ℂ) + (2 * Real.pi * z.2 : ℝ) * I))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply (χ.gammaFactor_differentiableAt_pos _ (by simp [densityVerticalPoint]; linarith)).continuousAt.comp
    exact (hs.add hw).continuousAt
  have hg0 : Continuous (fun z : ℝ × ℝ =>
      DirichletCharacter.gammaFactor χ.character (densityVerticalPoint (1 / 2) z.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply (χ.gammaFactor_differentiableAt_pos _ (by norm_num [densityVerticalPoint])).continuousAt.comp
    exact hs.continuousAt
  have hgn (z : ℝ × ℝ) :
      DirichletCharacter.gammaFactor χ.character (densityVerticalPoint (1 / 2) z.1) ≠ 0 := by
    intro h
    exact χ.gammaInverse_ne_zero (densityVerticalPoint (1 / 2) z.1) (by norm_num [densityVerticalPoint])
      (by simp only [PrimitiveComplexCharacter.gammaInverse, h, inv_zero])
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  unfold densitySquareKernel densityCompletedSquareWeight
  apply Continuous.div
  · exact (((differentiable_id.const_cpow (Or.inl hq)).continuous.comp hw).mul
      ((hg.div hg0 hgn).pow 2)).mul ((hw.pow 2).cexp)
  · exact hw
  · intro z h
    have hr := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_self, add_zero, zero_re] at hr
    exact hc.ne' hr

 theorem densityFiniteSquare_continuousOn (χ : PrimitiveComplexCharacter)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (T : ℝ) (hT : 1 ≤ T) :
    ContinuousOn (fun t : ℝ => ∑ n ∈ S,
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n) (Icc (-T) T) := by
  let a := densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + (1 : ℝ))
  let K : ℝ := densityKernelCost χ.modulus T 1 * ∑ n ∈ S, ‖a n‖
  let f : ℝ → ℝ → ℂ := fun t u => densitySquareKernel χ
    (densityVerticalPoint (1 / 2) t) ((1 : ℂ) + (2 * Real.pi * u : ℝ) * I) *
      densityCharacterPolynomial S a χ.character (t + u)
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hf : Continuous (Function.uncurry f) := by
    exact (densitySquareKernel_vertical_continuous χ 1 (by norm_num)).mul
      ((densityCharacterPolynomial_continuous S a χ.character).comp
        (continuous_fst.add continuous_snd))
  have hI : ContinuousOn (fun t => ∫ u : ℝ, f t u) (Icc (-T) T) := by
    apply continuousOn_of_dominated (bound := fun u => K * densityHalfGaussian u)
    · intro t _
      exact (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro t ht
      filter_upwards with u
      have hk := densitySquareKernel_common_bound χ.modulus χ.positive T 1 hT
        (by norm_num) (by norm_num) χ le_rfl t u (abs_le.mpr ht)
      have hp := densityCharacterPolynomial_norm S a χ.character (t + u)
      dsimp [f, K]
      rw [norm_mul]
      calc
        _ ≤ (densityKernelCost χ.modulus T 1 * densityHalfGaussian u) *
            (∑ n ∈ S, ‖a n‖) := mul_le_mul hk hp (norm_nonneg _)
              (mul_nonneg (densityKernelCost_pos χ.modulus χ.positive T 1 hT (by norm_num)).le
                (densityHalfGaussian_pos u).le)
        _ = _ := by ring
    · exact densityHalfGaussian_integrable.const_mul K
    · filter_upwards with u
      exact (hf.comp (continuous_id.prodMk continuous_const)).continuousOn
  have he (t : ℝ) : (∑ n ∈ S,
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n) = ∫ u : ℝ, f t u := by
    rw [densitySquareIntegralTerm_sum_fourier χ _ (by simp [densityVerticalPoint]) S hS 1
      (by norm_num) (by norm_num)]
    apply integral_congr_ae
    filter_upwards with u
    rw [densityFiniteKernel, densityFiniteMellin_original_polynomial χ S hS 1 t u]
    rfl
  simpa only [← he] using hI

end Ostmann

end OAI

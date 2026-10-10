import Mathlib.MeasureTheory.Integral.Prod
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityGaussianHybrid

namespace OAI

/-! # The Gaussian and height integrals for actual character polynomials -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def densityCharacterPolynomial {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t))

 theorem densityCharacterPolynomial_continuous {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) : Continuous (densityCharacterPolynomial S a χ) := by
  unfold densityCharacterPolynomial realAdditivePhase
  fun_prop

 theorem densityCharacterPolynomial_norm {q : ℕ} [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖densityCharacterPolynomial S a χ t‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul, norm_mul, norm_realAdditivePhase, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)

 theorem density_gaussian_character_integrable {q : ℕ} [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Integrable (fun z : ℝ × ℝ => densityHalfGaussian z.2 *
      ‖densityCharacterPolynomial S a χ (z.1 + z.2)‖ ^ 2)
      ((volume.restrict (Icc (-T) T)).prod volume) := by
  let μ := volume.restrict (Icc (-T) T)
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hbase : Integrable (fun z : ℝ × ℝ => densityHalfGaussian z.2) (μ.prod volume) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := μ)).mul_prod densityHalfGaussian_integrable
  have hc : Continuous (fun z : ℝ × ℝ => densityHalfGaussian z.2 *
      ‖densityCharacterPolynomial S a χ (z.1 + z.2)‖ ^ 2) := by
    exact (densityHalfGaussian_continuous.comp continuous_snd).mul
      (((densityCharacterPolynomial_continuous S a χ).comp (continuous_fst.add continuous_snd)).norm.pow 2)
  apply (hbase.const_mul ((∑ n ∈ S, ‖a n‖) ^ 2)).mono' hc.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityHalfGaussian_pos z.2).le (sq_nonneg _))]
  have h := pow_le_pow_left₀ (norm_nonneg _) (densityCharacterPolynomial_norm S a χ (z.1 + z.2)) 2
  nlinarith [densityHalfGaussian_pos z.2]

 theorem density_gaussian_character_fubini {q : ℕ} [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
      ‖densityCharacterPolynomial S a χ (t + u)‖ ^ 2) =
      ∫ u : ℝ, densityHalfGaussian u * ∫ t in Icc (-T) T,
        ‖densityCharacterPolynomial S a χ (t + u)‖ ^ 2 := by
  rw [integral_integral_swap (density_gaussian_character_integrable S a χ T)]
  apply integral_congr_ae
  filter_upwards with u
  rw [integral_const_mul]

 theorem gaussian_hybrid_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
          ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2) ≤
            C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gaussian_hybrid_multiplicative_large_sieve
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT a F hF
  have hi (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) (χ : DirichletCharacter ℂ q) :
      Integrable (fun u : ℝ => densityHalfGaussian u * ∫ t in Icc (-T) T,
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2) := by
    let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
    have h := (density_gaussian_character_integrable (Finset.Icc 1 N) a χ T).integral_prod_right
    simpa only [integral_const_mul] using h
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ u : ℝ, densityHalfGaussian u * ∫ t in Icc (-T) T,
          ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
      apply Finset.sum_congr rfl
      intro χ _
      exact density_gaussian_character_fubini (Finset.Icc 1 N) a χ T
    _ = ∫ u : ℝ, densityHalfGaussian u *
        (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q, ∫ t in Icc (-T) T,
          ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2) := by
      symm
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ (fun q hq => integrable_finsetSum _ (fun χ _ => hi q hq χ))]
      apply Finset.sum_congr rfl
      intro q hq
      exact integral_finsetSum _ (fun χ _ => hi q hq χ)
    _ ≤ _ := by simpa only [densityCharacterPolynomial] using hb N Q hQ T hT a F hF

end Ostmann

end OAI

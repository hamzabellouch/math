import OAI.NumberTheory.Ostmann.ZeroDensity.DensityShiftedHybrid
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityGaussianCauchy

namespace OAI

/-! # The hybrid mean square averaged over the Gaussian translation -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem densityHalfGaussian_first_moment :
    Integrable (fun u : ℝ => densityHalfGaussian u * |u|) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).norm
  convert h using 1
  funext u
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  unfold densityHalfGaussian
  rw [mul_comm]
  congr 1
  congr 1
  ring

 theorem gaussian_hybrid_multiplicative_large_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∫ u : ℝ, densityHalfGaussian u *
        (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
          ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
            a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * (t + u)))‖ ^ 2)) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := shifted_hybrid_multiplicative_large_sieve
  let G0 := ∫ u : ℝ, densityHalfGaussian u
  let G1 := ∫ u : ℝ, densityHalfGaussian u * |u|
  have hG0 : 0 < G0 := densityHalfGaussian_integral_pos
  have hG1 : 0 ≤ G1 := integral_nonneg (fun u => mul_nonneg (densityHalfGaussian_pos u).le (abs_nonneg u))
  refine ⟨C * (G0 + G1), by positivity, ?_⟩
  intro N Q hQ T hT a F hF
  let E := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
  let A := (N : ℝ) + (Q : ℝ) ^ 2 * T
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let H : ℝ → ℝ := fun u => ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
    ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
      a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * (t + u)))‖ ^ 2
  have hmaj : Integrable (fun u => densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E)) := by
    have he : (fun u => densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E)) =
        (fun u => (C * E * A) * densityHalfGaussian u +
          (C * E * (Q : ℝ) ^ 2) * (densityHalfGaussian u * |u|)) := by
      funext u
      ring
    rw [he]
    exact (densityHalfGaussian_integrable.const_mul _).add (densityHalfGaussian_first_moment.const_mul _)
  have hmean : (∫ u, densityHalfGaussian u * H u) ≤
      ∫ u, densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E) := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun u => mul_nonneg (densityHalfGaussian_pos u).le
        (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
          integral_nonneg (fun _ => sq_nonneg _)))))) hmaj
    apply Filter.Eventually.of_forall
    intro u
    have h := hb N Q hQ T u hT a F hF
    have he : (N : ℝ) + (Q : ℝ) ^ 2 * (T + |u|) = A + (Q : ℝ) ^ 2 * |u| := by dsimp [A]; ring
    rw [he] at h
    exact mul_le_mul_of_nonneg_left h (densityHalfGaussian_pos u).le
  have heval : (∫ u, densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E)) =
      C * E * (A * G0 + (Q : ℝ) ^ 2 * G1) := by
    have he : (fun u => densityHalfGaussian u * (C * (A + (Q : ℝ) ^ 2 * |u|) * E)) =
        (fun u => (C * E * A) * densityHalfGaussian u +
          (C * E * (Q : ℝ) ^ 2) * (densityHalfGaussian u * |u|)) := by
      funext u
      ring
    rw [he, integral_add (densityHalfGaussian_integrable.const_mul _)
      (densityHalfGaussian_first_moment.const_mul _), integral_const_mul, integral_const_mul]
    dsimp [G0, G1]
    ring
  change (∫ u, densityHalfGaussian u * H u) ≤ _
  apply hmean.trans
  rw [heval]
  have hQA : (Q : ℝ) ^ 2 ≤ A := by dsimp [A]; nlinarith [Nat.cast_nonneg (α := ℝ) N, sq_nonneg (Q : ℝ)]
  have hg := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQA hG1) (mul_nonneg hC.le hE)
  change _ ≤ C * (G0 + G1) * A * E
  nlinarith

end Ostmann

end OAI

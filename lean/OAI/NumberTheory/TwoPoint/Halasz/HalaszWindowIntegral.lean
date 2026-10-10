import OAI.NumberTheory.TwoPoint.Halasz.HalaszCauchySchwarz
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPerronWindowKernel

namespace OAI

/-! The central part of the prime--prime--smooth Perron integral.
The first prime factor uses its ordinary mean square and the second its
global Cauchy-weighted mean square. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset

lemma halasz_vertical_norm (t : ℝ) :
    ‖(1 : ℂ) + (t : ℂ) * I‖ = Real.sqrt (1 + t ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply, pow_two]

lemma halasz_window_middle_bound {x δ T A : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (P Q F : ℝ → ℂ) (hP : Continuous P) (hQ : Continuous Q)
    (hF : ∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ A) :
    ‖∫ t in -T..T, P t * Q t * F t *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)‖ ≤
      (4 * x * A) * (Real.sqrt (∫ t in -T..T, ‖P t‖ ^ 2) *
        Real.sqrt (∫ t in -T..T, ‖Q t‖ ^ 2 * (1 + t ^ 2)⁻¹)) := by
  let G := fun t : ℝ => ‖P t‖ * ‖Q t‖ / Real.sqrt (1 + t ^ 2)
  have hG : Continuous G := by
    exact (hP.norm.mul hQ.norm).div ((continuous_const.add (continuous_id.pow 2)).sqrt)
      (fun t => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖P t * Q t * F t * halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)‖ ≤
        (4 * x * A) * G t := by
    rw [norm_mul, norm_mul, norm_mul]
    have hk := halasz_perron_window_bound hx hδ hδ1 t
    rw [halasz_vertical_norm] at hk
    calc
      _ ≤ (‖P t‖ * ‖Q t‖ * A) * (4 * x / Real.sqrt (1 + t ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hF t ht) (by positivity)) hk
          (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [G]; ring
  calc
    _ ≤ ∫ t in -T..T, (4 * x * A) * G t := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Filter.Eventually.of_forall (fun t ht => hbound t ⟨ht.1.le, ht.2⟩))
        ((hG.const_mul _).intervalIntegrable _ _)
    _ = (4 * x * A) * ∫ t in -T..T, G t := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (halasz_weighted_integral_cauchy_schwarz (by linarith) P Q hP hQ) (by positivity)

theorem halasz_prime_window_middle : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (x δ T A : ℝ), 0 < x → 0 < δ → δ ≤ 1 → B ≤ T → 0 ≤ A →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ (a b : ℕ → ℂ) (F : ℝ → ℂ),
      (∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ A) →
      ‖∫ t in -T..T,
        mrtExponentialPolynomial P (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
          (fun p => -Real.log (p : ℝ)) t *
        mrtExponentialPolynomial Q (fun q => b q * ((Real.log (q : ℝ) / q : ℝ) : ℂ))
          (fun q => -Real.log (q : ℝ)) t * F t *
        halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)‖ ≤
        (C * x * A) * (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) := by
  obtain ⟨C₁, B, hC₁, hB, hfirst⟩ := halasz_prime_mean_square
  obtain ⟨C₂, hC₂, hsecond⟩ := halasz_prime_mean_square_cauchy
  refine ⟨4 * Real.sqrt C₁ * Real.sqrt C₂, B, by positivity, hB, ?_⟩
  intro x δ T A hx hδ hδ1 hBT hA P Q hP hQ a b F hF
  have hT : 0 ≤ T := (by linarith : (0 : ℝ) ≤ B).trans hBT
  let P₁ := mrtExponentialPolynomial P
    (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ)) (fun p => -Real.log (p : ℝ))
  let Q₁ := mrtExponentialPolynomial Q
    (fun q => b q * ((Real.log (q : ℝ) / q : ℝ) : ℂ)) (fun q => -Real.log (q : ℝ))
  have hp : (∫ t in -T..T, ‖P₁ t‖ ^ 2) ≤
      C₁ * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p) := hfirst T P hBT hP a
  have hqi := halasz_cauchy_polynomial_integrable Q
    (fun q => b q * ((Real.log (q : ℝ) / q : ℝ) : ℂ)) (fun q => -Real.log (q : ℝ))
  have hq : (∫ t in -T..T, ‖Q₁ t‖ ^ 2 * (1 + t ^ 2)⁻¹) ≤
      C₂ * ∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q) := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    exact (setIntegral_le_integral hqi (Filter.Eventually.of_forall (fun t => by positivity))).trans
      (hsecond Q hQ b)
  have hmid := halasz_window_middle_bound hx hδ hδ1 hT hA P₁ Q₁ F
    (halasz_polynomial_continuous P _ _) (halasz_polynomial_continuous Q _ _) hF
  apply hmid.trans
  calc
    _ ≤ (4 * x * A) *
        (Real.sqrt (C₁ * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (C₂ * ∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hp) (Real.sqrt_le_sqrt hq)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by rw [Real.sqrt_mul hC₁.le, Real.sqrt_mul hC₂.le]; ring

end TwoPointCorrelations

end OAI

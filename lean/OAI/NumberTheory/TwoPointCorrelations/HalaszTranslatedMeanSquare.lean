import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimeMeanSquare

namespace OAI

/-! Translation of the prime mean square, including unit windows. The
translation only changes the phases of the arbitrary prime coefficients. -/

namespace TwoPointCorrelations

open Finset MeasureTheory

lemma halasz_polynomial_translate {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (u t : ℝ) :
    mrtExponentialPolynomial S
      (fun i => a i * Complex.exp (((freq i * u : ℝ) : ℂ) * Complex.I)) freq t =
      mrtExponentialPolynomial S a freq (t + u) := by
  unfold mrtExponentialPolynomial
  apply sum_congr rfl
  intro i _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma halasz_polynomial_continuous {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) : Continuous (mrtExponentialPolynomial S a freq) := by
  unfold mrtExponentialPolynomial
  fun_prop

theorem halasz_prime_mean_square_translated : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (T u : ℝ) (P : Finset ℕ), B ≤ T →
      (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) → ∀ a : ℕ → ℂ,
      (∫ t in (u - T)..(u + T),
        ‖mrtExponentialPolynomial P
          (fun p => a p * ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ))
          (fun p => -Real.log (p : ℝ)) t‖ ^ 2) ≤
        C * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / (p : ℝ)) := by
  obtain ⟨C, B, hC, hB, hm⟩ := halasz_prime_mean_square
  refine ⟨C, B, hC, hB, ?_⟩
  intro T u P hBT hP a
  let phase := fun p : ℕ => Complex.exp (((-Real.log (p : ℝ) * u : ℝ) : ℂ) * Complex.I)
  let D := mrtExponentialPolynomial P
    (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ)) (fun p => -Real.log (p : ℝ))
  have he (t : ℝ) : mrtExponentialPolynomial P
      (fun p => (a p * phase p) * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
      (fun p => -Real.log (p : ℝ)) t = D (t + u) := by
    dsimp only [D]
    rw [← halasz_polynomial_translate]
    unfold mrtExponentialPolynomial
    apply sum_congr rfl
    intro p _
    dsimp [phase]
    ring
  have hp (p : ℕ) : ‖a p * phase p‖ = ‖a p‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h := hm T P hBT hP (fun p => a p * phase p)
  simp_rw [he, hp] at h
  have ht := intervalIntegral.integral_comp_add_right (fun t => ‖D t‖ ^ 2) u
    (a := -T) (b := T)
  rw [ht] at h
  simpa only [sub_eq_add_neg, add_comm] using h

end TwoPointCorrelations

end OAI

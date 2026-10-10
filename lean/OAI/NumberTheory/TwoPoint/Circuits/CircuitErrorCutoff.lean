import OAI.NumberTheory.TwoPoint.Circuits.CircuitSemiExact

namespace OAI

/-! The algebraic error-cutoff step of Braverman's Lemma 10. A Fourier
approximation of the exceptional event suppresses the large polynomial
values on that event while preserving exact zeros. -/

namespace TwoPointCorrelations

open scoped Classical

noncomputable def exceptionalExtension {n : ℕ} (F : BooleanCube n → ℝ)
    (E : BooleanCube n → Bool) (x : BooleanCube n) : ℝ :=
  if E x then 1 else F x

noncomputable def errorCutoffPolynomial {n : ℕ} (P T : BooleanCube n → ℝ)
    (x : BooleanCube n) : ℝ := P x * (1 - T x)

lemma exceptionalExtension_boolean {n : ℕ} {F : BooleanCube n → ℝ}
    (hF : ∀ x, F x = 0 ∨ F x = 1) (E : BooleanCube n → Bool) (x : BooleanCube n) :
    exceptionalExtension F E x = 0 ∨ exceptionalExtension F E x = 1 := by
  unfold exceptionalExtension
  split_ifs
  · exact Or.inr rfl
  · exact hF x

lemma errorCutoffPolynomial_zero {n : ℕ} {F P T : BooleanCube n → ℝ}
    {E : BooleanCube n → Bool} (he : ∀ x, E x = false → P x = F x)
    (x : BooleanCube n) (hx : exceptionalExtension F E x = 0) :
    errorCutoffPolynomial P T x = 0 := by
  have hE : E x = false := by
    cases h : E x <;> simp_all [exceptionalExtension]
  have hF : F x = 0 := by simpa [exceptionalExtension, hE] using hx
  simp [errorCutoffPolynomial, he x hE, hF]

lemma errorCutoffPolynomial_degree {n p q : ℕ} {P T : BooleanCube n → ℝ}
    (hP : WalshDegreeLE P p) (hT : WalshDegreeLE T q) :
    WalshDegreeLE (errorCutoffPolynomial P T) (p + q) :=
  hP.mul ((WalshDegreeLE.const 1 q).sub hT)

lemma errorCutoffPolynomial_sq_bound {n : ℕ} {F P T : BooleanCube n → ℝ}
    {E : BooleanCube n → Bool} (hF : ∀ x, F x = 0 ∨ F x = 1)
    (he : ∀ x, E x = false → P x = F x) {B : ℝ} (hB : 1 ≤ B)
    (hP : ∀ x, |P x| ≤ B) (x : BooleanCube n) :
    (exceptionalExtension F E x - errorCutoffPolynomial P T x) ^ 2 ≤
      2 * (if E x then (1 : ℝ) else 0) +
        2 * B ^ 2 * ((if E x then (1 : ℝ) else 0) - T x) ^ 2 := by
  have hp : (P x) ^ 2 ≤ B ^ 2 := by
    have ha := abs_le.mp (hP x)
    nlinarith
  have hBsq : 1 ≤ B ^ 2 := by nlinarith
  cases hE : E x
  · have heq := he x hE
    rcases hF x with hf | hf
    · simp [exceptionalExtension, errorCutoffPolynomial, hE, heq, hf]
      positivity
    · simp only [exceptionalExtension, errorCutoffPolynomial, hE,
        Bool.false_eq_true, ite_false, heq, hf, one_mul, mul_zero, zero_add]
      have hh := mul_le_mul_of_nonneg_right hBsq (sq_nonneg (T x))
      nlinarith only [hh, sq_nonneg (T x)]
  · simp only [exceptionalExtension, errorCutoffPolynomial, hE, ite_true]
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg (1 - T x))
    nlinarith only [hh, sq_nonneg (1 + P x * (1 - T x))]

theorem errorCutoffPolynomial_mean_sq {n : ℕ} {F P T : BooleanCube n → ℝ}
    {E : BooleanCube n → Bool} (hF : ∀ x, F x = 0 ∨ F x = 1)
    (he : ∀ x, E x = false → P x = F x) {B δ ε : ℝ} (hB : 1 ≤ B)
    (hP : ∀ x, |P x| ≤ B)
    (hE : cubeAverage (fun x => if E x then (1 : ℝ) else 0) ≤ δ)
    (hT : cubeAverage (fun x => ((if E x then (1 : ℝ) else 0) - T x) ^ 2) ≤ ε) :
    cubeAverage (fun x =>
      (exceptionalExtension F E x - errorCutoffPolynomial P T x) ^ 2) ≤
        2 * δ + 2 * B ^ 2 * ε := by
  have hh := cubeAverage_mono (errorCutoffPolynomial_sq_bound (T := T) hF he hB hP)
  rw [cubeAverage_add, cubeAverage_mul_const, cubeAverage_mul_const] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num))
    (mul_le_mul_of_nonneg_left hT (by positivity)))

end TwoPointCorrelations

end OAI

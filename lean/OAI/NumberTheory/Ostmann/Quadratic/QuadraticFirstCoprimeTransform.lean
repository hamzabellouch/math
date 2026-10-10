import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstSignedTransform
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyTwist

namespace OAI

/-! # The exact second-Poisson input inside each signed first-transform term -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

theorem quadratic_first_square_term {q e : ℕ} (hq : 0 < q)
    {M : ℝ} (hM : 0 < M) (ψ : 𝓢(ℝ, ℂ)) (a : ℤ) (b : ℕ) :
    (∑' c : ℕ+, (jacobiSym ((e : ℤ) * (a * (c : ℕ) ^ 2 * b)) q : ℂ) *
      𝓕 ψ (((a * (c : ℕ) ^ 2 * b : ℤ) : ℝ) * M / ((e : ℝ) * q))) =
    ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
      ∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
        𝓕 ψ ((a : ℝ) * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M)) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro c
  have harg : (((a * (c : ℕ) ^ 2 * b : ℤ) : ℝ) * M / ((e : ℝ) * q)) =
      (a : ℝ) * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M) := by
    push_cast
    field_simp
  rw [harg]
  have hj := quadratic_frequency_character ((e : ℤ) * a) (c : ℕ) b
    hq.ne'
  have heq : (e : ℤ) * (a * (c : ℕ) ^ 2 * b) =
      ((e : ℤ) * a) * (c : ℕ) ^ 2 * b := by ring
  rw [heq, hj, quadratic_principal_nat, jacobiSym.mul_left, Int.cast_mul]
  by_cases hc : (c : ℕ).Coprime q
  · rw [ite_eq_left hc, ite_eq_left hc]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]
    ring

theorem quadratic_first_signed_coprime {q e : ℕ} (hq : 1 < q) (he : 0 < e)
    {M : ℝ} (hM : 0 < M) (ψ : 𝓢(ℝ, ℂ)) :
    (∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
      𝓕 ψ ((h : ℝ) * M / ((e : ℝ) * q))) =
    ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑' b : QuadraticOddKernel,
      ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym (b.val : ℕ) q : ℂ)) *
        ∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
          𝓕 ψ ((a : ℝ) * (b.val : ℕ) * (c : ℝ) ^ 2 / ((e : ℝ) * q / M)) := by
  rw [quadratic_first_signed_transform hq he hM ψ]
  apply Finset.sum_congr rfl
  intro a _
  apply tsum_congr
  intro b
  exact quadratic_first_square_term (by omega) hM ψ a b.val

end Ostmann

end OAI

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by
  by_cases h0 : z = 0
  · simp [h0]
  have h3 : z ^ 3 = 1 := by
    apply mul_right_cancel₀ h0
    simpa only [← pow_succ, one_mul] using hz
  have hn := Complex.norm_eq_one_of_pow_eq_one h3 (by decide : (3 : ℕ) ≠ 0)
  change z ^ 2 = (starRingEnd ℂ) z
  rw [← Complex.inv_eq_conj hn]
  apply mul_right_cancel₀ h0
  rw [inv_mul_cancel₀ h0]
  simpa only [← pow_succ] using h3

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_inv_eq_square (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) :
    χ⁻¹ = χ ^ 2 := by
  calc
    χ⁻¹ = χ⁻¹ * χ ^ 3 := by rw [hχ, mul_one]
    _ = χ ^ 2 := by group

theorem cubic_square_eq_star (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 2 = star (χ x) := by
  rw [MulChar.star_apply', cubic_inv_eq_square χ hχ, MulChar.pow_apply' _ (by decide)]

omit [Finite Rˣ] in
theorem cubic_fourth_eq (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]

omit [Finite Rˣ] in
theorem cubic_cube_eq_mask (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ (x ^ 3) = if IsUnit x then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ]
  by_cases hx : IsUnit x
  · rw [ite_eq_left hx, MulChar.one_apply hx]
  · rw [ite_eq_right hx, MulChar.map_nonunit _ hx]

theorem cubic_row_decomposition (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1)
    (a b c : R) :
    χ (a * b ^ 2 * c ^ 3) =
      χ a * star (χ b) * (if IsUnit c then 1 else 0) := by
  rw [map_mul, map_mul, map_pow, cubic_square_eq_star χ hχ,
    cubic_cube_eq_mask χ hχ]

omit [Finite Rˣ] in
theorem cubic_norm_le_one (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · have hc : χ x ^ 3 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ, MulChar.one_apply hx]
    exact (Complex.norm_eq_one_of_pow_eq_one hc (by decide)).le
  · rw [MulChar.map_nonunit _ hx, norm_zero]
    exact zero_le_one

theorem row_decomposition_sum {ι M : Type*} [CommMonoid M]
    (S : Finset ι) (coef : ι → ℂ) (ρ : ι → M →* R)
    (χ : ι → MulChar R ℂ) (hχ : ∀ n ∈ S, χ n ^ 3 = 1)
    (a b c : M) :
    (∑ n ∈ S, coef n * χ n (ρ n (a * b ^ 2 * c ^ 3))) =
      ∑ n ∈ S,
        (coef n * star (χ n (ρ n b)) *
          (if IsUnit (ρ n c) then 1 else 0)) * χ n (ρ n a) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  have hmap : ρ n (a * b ^ 2 * c ^ 3) =
      ρ n a * (ρ n b) ^ 2 * (ρ n c) ^ 3 := by simp only [map_mul, map_pow]
  rw [hmap, cubic_row_decomposition (χ n) (hχ n hn)]
  ring

omit [Finite Rˣ] in
theorem extracted_coefficients_energy_le {ι : Type*}
    (S : Finset ι) (coef : ι → ℂ) (χ : ι → MulChar R ℂ)
    (hχ : ∀ n ∈ S, χ n ^ 3 = 1) (b c : ι → R) :
    (∑ n ∈ S, ‖coef n * star (χ n (b n)) *
      (if IsUnit (c n) then (1 : ℂ) else 0)‖ ^ 2) ≤
      ∑ n ∈ S, ‖coef n‖ ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro n hn
  by_cases hc : IsUnit (c n)
  · simp only [ite_eq_left hc, mul_one, norm_mul, norm_star]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_right (norm_nonneg _) (cubic_norm_le_one (χ n) (hχ n hn) _)
  · simp only [ite_eq_right hc, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

end
end SevenEighths.CubicSieve

end OAI

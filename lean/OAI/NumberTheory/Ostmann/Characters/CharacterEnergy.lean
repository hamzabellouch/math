import OAI.NumberTheory.Ostmann.Characters.GaussFourier

namespace OAI

/-!
# Energy and the principal-character correction

All characters, including the principal one, vanish at zero. Multiplying
by a character cannot increase Fourier energy, and the principal twist
subtracts the zero-point contribution from every Fourier coefficient.
-/

namespace Ostmann

open scoped BigOperators

theorem norm_mulChar_le_one {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (x : ZMod p) : ‖χ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · exact (norm_mulChar_unit χ (Units.mk0 x hx)).le

theorem additiveFourier_character_energy_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    (∑ a : ZMod p, ‖additiveFourier (fun x => f x * χ x) a‖ ^ 2) ≤
      ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 := by
  rw [additiveFourier_parseval, additiveFourier_parseval]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg p))
  apply Finset.sum_le_sum
  intro x _
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_mulChar_le_one χ x)

theorem additiveFourier_principal_twist {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f x * (1 : MulChar (ZMod p) ℂ) x) a =
      additiveFourier f a - (p : ℂ)⁻¹ * f 0 := by
  classical
  have hpoint : (fun x => f x * (1 : MulChar (ZMod p) ℂ) x) =
      (fun x => f x - if x = 0 then f 0 else 0) := by
    funext x
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · simp only [hx, ite_false, sub_zero]
      rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx), mul_one]
  rw [hpoint, additiveFourier_sub]
  congr 1
  simp [additiveFourier_apply]

end Ostmann

end OAI

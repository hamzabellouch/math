import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalRankOneHomology
import Mathlib.Algebra.Category.ModuleCat.Basic

namespace OAI

/-! # Integral properties of a rational line -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory

theorem rational_commensurable (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y := by
  have hden (q : ℚ) : (q.den : ℚ) * q = q.num := by
    calc
      _ = (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) :=
        congrArg (fun z : ℚ => (q.den : ℚ) * z) q.num_div_den.symm
      _ = q.num := mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr q.den_nz)
  refine ⟨y.num * x.den, x.num * y.den,
    mul_ne_zero (Rat.num_ne_zero.mpr hy) (Int.natCast_ne_zero.mpr x.den_nz),
    mul_ne_zero (Rat.num_ne_zero.mpr hx) (Int.natCast_ne_zero.mpr y.den_nz), ?_⟩
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  calc
    (y.num : ℚ) * x.den * x = y.num * ((x.den : ℚ) * x) := by ring
    _ = y.num * x.num := by rw [hden]
    _ = x.num * y.num := mul_comm _ _
    _ = x.num * ((y.den : ℚ) * y) := by rw [hden]
    _ = (x.num : ℚ) * y.den * y := by ring

theorem rationalLine_properties (M : ModuleCat ℤ) (e : M ≃ₗ[ℤ] ℚ) :
    (∃ x : M, x ≠ 0) ∧
    (∀ (a : ℤ) (x : M), a • x = 0 → a = 0 ∨ x = 0) ∧
    (∀ x y : M, x ≠ 0 → y ≠ 0 →
      ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) := by
  refine ⟨⟨e.symm 1, ?_⟩, ?_, ?_⟩
  · intro h
    have he := congrArg e h
    exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using he)
  · intro a x h
    have he := congrArg e h
    simp only [map_zsmul, map_zero, zsmul_eq_mul] at he
    rcases mul_eq_zero.mp he with ha | hx
    · exact Or.inl (Int.cast_eq_zero.mp ha)
    · exact Or.inr (e.injective (hx.trans (map_zero e).symm))
  · intro x y hx hy
    have hx' : e x ≠ 0 := fun h => hx (e.injective (h.trans (map_zero e).symm))
    have hy' : e y ≠ 0 := fun h => hy (e.injective (h.trans (map_zero e).symm))
    obtain ⟨a, b, ha, hb, he⟩ := rational_commensurable (e x) (e y) hx' hy'
    exact ⟨a, b, ha, hb, e.injective (by simpa only [map_zsmul] using he)⟩

end PolycyclicRecognition

end

end OAI

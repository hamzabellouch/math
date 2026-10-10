import OAI.Analysis.Pureness.Operators.OrthogonalOperatorSums

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped BigOperators
variable {B E : Type*} [CStarAlgebra B] [CStarAlgebra E]

def unitaryAverage {n : ℕ} (u : Fin n → unitary B) (x : B) : B :=
  (n : ℂ)⁻¹ • ∑ i, (u i : B)*x*star (u i : B)

lemma unitaryAverage_sub {n : ℕ} (u : Fin n → unitary B) (x y : B) :
    unitaryAverage u (x-y) = unitaryAverage u x-unitaryAverage u y := by
  simp only [unitaryAverage, mul_sub, sub_mul, Finset.sum_sub_distrib, smul_sub]

lemma unitaryAverage_norm_le {n : ℕ} (u : Fin n → unitary B) (x : B) :
    ‖unitaryAverage u x‖ ≤ ‖x‖ := by
  by_cases hn : n = 0
  · subst n
    simp [unitaryAverage]
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc
    _ = (n : ℝ)⁻¹ * ‖∑ i, (u i : B)*x*star (u i : B)‖ := by
      simp only [unitaryAverage, norm_smul, norm_inv, Complex.norm_natCast]
    _ ≤ (n : ℝ)⁻¹ * ∑ i, ‖(u i : B)*x*star (u i : B)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = ‖x‖ := by
      simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
        CStarRing.norm_coe_unitary_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hnr, one_mul]

lemma unitaryAverage_fixed {n : ℕ} (hn : n ≠ 0) (u : Fin n → unitary B) (x : B)
    (hx : ∀ i, Commute (u i : B) x) : unitaryAverage u x = x := by
  have he (i : Fin n) : (u i : B)*x*star (u i : B) = x := by
    rw [(hx i).eq, mul_assoc, ← Unitary.coe_star, Unitary.coe_mul_star_self, mul_one]
  simp only [unitaryAverage, he, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]

lemma unitaryAverage_map_zero {n : ℕ} (u : Fin n → unitary B)
    (Φ : B →⋆ₐ[ℂ] E) (x : B) (hx : Φ x = 0) : Φ (unitaryAverage u x) = 0 := by
  simp only [unitaryAverage, map_smul, map_sum, map_mul, hx, mul_zero, zero_mul,
    Finset.sum_const_zero, smul_zero]
end CuntzPureness

end

end OAI

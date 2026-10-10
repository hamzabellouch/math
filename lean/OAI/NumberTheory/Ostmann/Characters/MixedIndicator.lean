import OAI.NumberTheory.Ostmann.Characters.Gauss

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
variable {p : ℕ} [Fact p.Prime]

theorem norm_character_of_ne_zero (χ : MulChar (ZMod p) ℂ)
    {x : ZMod p} (hx : x ≠ 0) : ‖χ x‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf χ, χ.orderOf_pos, ?_⟩
  rw [← χ.pow_apply' χ.orderOf_pos.ne', pow_orderOf_eq_one]
  exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)

theorem norm_character_le_one (χ : MulChar (ZMod p) ℂ) (x : ZMod p) : ‖χ x‖ ≤ 1 := by
  by_cases h : x = 0
  · simp [h, MulChar.map_zero]
  · exact (norm_character_of_ne_zero χ h).le

theorem sum_translated_eq_zero (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (a : ZMod p) : ∑ x : ZMod p, χ (x-a) = 0 := by
  simpa only [Units.val_one, one_mul, sub_eq_add_neg] using
    sum_affine_eq_zero χ hχ 1 (-a)

theorem normalizedIndicator_character_sum (S : Finset (ZMod p))
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    (∑ x : ZMod p, (Supply.normalizedIndicator S x : ℂ) * χ (a-x)) =
      χ (-1) / (Real.sqrt (Supply.density S * (1-Supply.density S)) : ℂ) *
        ∑ x ∈ S, χ (x-a) := by
  have hc (x : ZMod p) : (Supply.normalizedIndicator S x : ℂ) =
      ((if x ∈ S then (1 : ℂ) else 0) - (Supply.density S : ℂ)) /
        (Real.sqrt (Supply.density S * (1-Supply.density S)) : ℂ) := by
    unfold Supply.normalizedIndicator Supply.centeredIndicator
    push_cast
    split_ifs <;> rfl
  have he (x : ZMod p) : a-x = -1*(x-a) := by ring
  have ht (x : ZMod p) :
      (Supply.normalizedIndicator S x : ℂ) * χ (a-x) =
        (χ (-1) / (Real.sqrt (Supply.density S * (1-Supply.density S)) : ℂ)) *
          (if x ∈ S then χ (x-a) else 0) -
        ((Supply.density S : ℂ) * χ (-1) /
          (Real.sqrt (Supply.density S * (1-Supply.density S)) : ℂ)) * χ (x-a) := by
    rw [hc, he, map_mul]
    split_ifs <;> ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_translated_eq_zero χ hχ a]
  simp

theorem mixed_additiveTransform (S : Finset (ZMod p))
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    FiniteField.mixedCorrelation (Supply.additiveTransform S) χ a =
      ((p : ℂ) * (Real.sqrt p : ℂ))⁻¹ * gaussSum χ ZMod.stdAddChar *
        (χ⁻¹ (-1) / (Real.sqrt (Supply.density S * (1-Supply.density S)) : ℂ) *
          ∑ x ∈ S, χ⁻¹ (x-a)) := by
  rw [Supply.additiveTransform, mixed_unitaryDFT _ χ hχ,
    normalizedIndicator_character_sum S χ⁻¹ (inv_ne_one.mpr hχ) a]

theorem mixed_unitaryDFT_principal (f : ZMod p → ℂ) (hf : ∑ x, f x = 0)
    (a : ZMod p) :
    FiniteField.mixedCorrelation (Supply.unitaryDFT f) 1 a = f a / (Real.sqrt p : ℂ) := by
  have hz : Supply.unitaryDFT f 0 = 0 := by
    simp only [Supply.unitaryDFT, ZMod.dft_apply_zero, hf, zero_div]
  have he (v : ZMod p) : Supply.unitaryDFT f v * (1 : MulChar (ZMod p) ℂ) v =
      Supply.unitaryDFT f v := by
    by_cases hv : v = 0
    · simp [hv, hz]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hv), mul_one]
  unfold FiniteField.mixedCorrelation FiniteField.mean
  simp_rw [he]
  rw [FiniteField.fourier_inversion f a]
  simp only [Supply.unitaryDFT, FiniteField.fourier,
    Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mul_comm a v]
  ring

theorem mixed_additiveTransform_principal (S : Finset (ZMod p)) (a : ZMod p) :
    FiniteField.mixedCorrelation (Supply.additiveTransform S) 1 a =
      (Supply.normalizedIndicator S a : ℂ) / (Real.sqrt p : ℂ) := by
  apply mixed_unitaryDFT_principal
  rw [← Complex.ofReal_sum, Supply.sum_normalizedIndicator]
  rfl
end Ostmann.Characters

end

end OAI

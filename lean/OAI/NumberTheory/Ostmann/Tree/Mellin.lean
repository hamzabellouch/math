import Mathlib

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F]
variable [DecidableEq F]
local instance : Fintype (MulChar F ℂ) := Fintype.ofFinite _

def mellin (f : Fˣ → ℂ) (χ : MulChar F ℂ) : ℂ :=
  (Fintype.card Fˣ : ℂ)⁻¹ * ∑ u, f u * conj (χ u)

theorem mulChar_card : Fintype.card (MulChar F ℂ) = Fintype.card Fˣ := by
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity F ℂ

theorem sum_mulChar_apply (u : Fˣ) :
    ∑ χ : MulChar F ℂ, χ u = if u=1 then (Fintype.card Fˣ : ℂ) else 0 := by
  classical
  by_cases hu : u=1
  · simp [hu, mulChar_card]
  · simp only [hu, ite_false]
    have huv : (u : F) ≠ 1 := by
      intro h
      exact hu (Units.ext h)
    obtain ⟨ψ,hψ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity F ℂ huv
    apply eq_zero_of_mul_eq_self_left hψ
    rw [Finset.mul_sum]
    simp_rw [← MulChar.mul_apply]
    exact (Equiv.mulLeft ψ).bijective.sum_comp (fun χ : MulChar F ℂ => χ u)

omit [DecidableEq F] in
theorem conj_mulChar_apply (χ : MulChar F ℂ) (u : Fˣ) :
    conj (χ u) = χ (u⁻¹ : Fˣ) := by
  change star (χ (u : F)) = χ (u⁻¹ : Fˣ)
  rw [MulChar.star_apply', MulChar.inv_apply']
  rw [Units.val_inv_eq_inv_val]

theorem sum_mulChar_kernel (u v : Fˣ) :
    ∑ χ : MulChar F ℂ, conj (χ u) * χ v =
      if u=v then (Fintype.card Fˣ : ℂ) else 0 := by
  classical
  simp_rw [conj_mulChar_apply, ← map_mul, ← Units.val_mul]
  rw [sum_mulChar_apply]
  simp only [inv_mul_eq_one]

theorem mellin_inversion (f : Fˣ → ℂ) (v : Fˣ) :
    ∑ χ : MulChar F ℂ, mellin f χ * χ v = f v := by
  classical
  simp only [mellin, Finset.sum_mul, mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext u; rw [← Finset.mul_sum, ← Finset.mul_sum, sum_mulChar_kernel]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hN : (Fintype.card Fˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem mellin_parseval_complex (f : Fˣ → ℂ) :
    ∑ χ : MulChar F ℂ, conj (mellin f χ) * mellin f χ =
      (Fintype.card Fˣ : ℂ)⁻¹ * ∑ u, conj (f u) * f u := by
  calc
    _ = ∑ χ : MulChar F ℂ, ∑ u : Fˣ,
        (Fintype.card Fˣ : ℂ)⁻¹ * conj (f u) * (mellin f χ * χ u) := by
      apply Finset.sum_congr rfl
      intro χ _
      have hm : conj (mellin f χ) =
          (Fintype.card Fˣ : ℂ)⁻¹ * ∑ u, conj (f u) * χ u := by
        simp [mellin]
      rw [hm, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = (Fintype.card Fˣ : ℂ)⁻¹ * ∑ u, conj (f u) * f u := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.mul_sum, mellin_inversion]
      ring

theorem mellin_parseval (f : Fˣ → ℂ) :
    ∑ χ : MulChar F ℂ, ‖mellin f χ‖ ^ 2 =
      (Fintype.card Fˣ : ℝ)⁻¹ * ∑ u, ‖f u‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.conj_mul', Complex.ofReal_pow] using mellin_parseval_complex f

end
end Ostmann.FiniteField

end OAI

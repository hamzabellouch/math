import OAI.NumberTheory.Ostmann.Characters.Basic
import OAI.NumberTheory.Ostmann.Supply.Fourier

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters

section Field
variable {F : Type*} [Field F] [Fintype F]

theorem gauss_transform (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (a : F) :
    (∑ v : F, χ v * ψ (a*v)) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : a = 0
  · simp [ha, MulChar.map_zero, MulChar.sum_eq_zero_of_ne_one hχ]
  · exact gaussSum_mulShift_eq χ ψ (Units.mk0 a ha)

theorem norm_gaussSum (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hn := congrArg norm h
  simp only [norm_mul, norm_star, Complex.norm_natCast] at hn
  rw [← Real.sqrt_sq (norm_nonneg (gaussSum χ ψ)), pow_two, hn]
end Field

section Prime
variable {p : ℕ} [Fact p.Prime]

theorem mixed_unitaryDFT (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (hχ : χ ≠ 1) (a : ZMod p) :
    FiniteField.mixedCorrelation (Supply.unitaryDFT f) χ a =
      ((p : ℂ) * (Real.sqrt p : ℂ))⁻¹ * gaussSum χ ZMod.stdAddChar *
        ∑ x : ZMod p, f x * χ⁻¹ (a-x) := by
  unfold FiniteField.mixedCorrelation FiniteField.mean Supply.unitaryDFT
  simp only [ZMod.dft_apply, smul_eq_mul, div_eq_mul_inv,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hf (x : ZMod p) :
      (∑ v : ZMod p,
        (ZMod.stdAddChar (-(x*v)) * f x * (Real.sqrt p : ℂ)⁻¹) * χ v *
          ZMod.stdAddChar (a*v)) =
      f x * (Real.sqrt p : ℂ)⁻¹ *
        (χ⁻¹ (a-x) * gaussSum χ ZMod.stdAddChar) := by
    rw [← gauss_transform χ hχ ZMod.stdAddChar (a-x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [sub_mul, AddChar.map_sub_eq_div]
    rw [AddChar.map_neg_eq_inv]
    ring
  simp_rw [hf]
  simp only [mul_inv_rev, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring
end Prime
end Ostmann.Characters

end

end OAI

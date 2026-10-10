import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.FourAffineKernel
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentSigns

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma fourReverseRectangle (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    rectangular (fun i j=>(a i j:ℤ))
      (fun i j x y=>-fourAffine d₁ e₁ d₂ e₂ j i (.inr y) (.inl x))=
    (-1 : (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) ^
      (∑ i,∑ j,(a i j:ℤ)*(d₂ i:ℤ)*(e₁ j:ℤ)) *
    rectangular (fun i j=>(a j i:ℤ))
      (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)) := by
  conv_lhs => arg 2; ext i j x y; rw [←neg_one_mul]
  rw [rectangular_scalar_mul]
  simp only [Fintype.card_fin]
  congr 1
  exact rectangular_transpose (fun i j=>(a j i:ℤ)) _

lemma fourCrossAffineUnit_signed (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourCrossAffineUnit a d₁ e₁ d₂ e₂=
    (-1 : (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) ^ eulerForm a d₂ e₁ *
      (rectangular (fun i j : I=>if i=j then 1 else 0)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) *
      rectangular (fun i j : I=>if i=j then 1 else 0)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) *
      rectangular (fun i j=>(a i j:ℤ))
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inr y)) *
      rectangular (fun i j=>(a j i:ℤ))
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y))) := by
  rw [fourCrossAffineUnit,fourReverseRectangle]
  have he : ((∑ i,e₁ i*d₂ i : ℕ):ℤ)-(∑ i,∑ j,(a i j:ℤ)*(d₂ i:ℤ)*(e₁ j:ℤ))=eulerForm a d₂ e₁ := by
    simp only [eulerForm,Nat.cast_sum,Nat.cast_mul]
    congr 1
    exact Finset.sum_congr rfl (fun i hi=>mul_comm _ _)
  rw [←he,←unit_neg_one_zpow_sub,zpow_natCast]
  exact mul_sign_collect (G := (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) _ _ _ _ _ _

lemma fourKernel_cancellation (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
      fourCrossAffineUnit a d₁ e₁ d₂ e₂=
    (-1 : (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) ^ eulerForm a d₂ e₁ *
      (rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) *
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) *
      (rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)) *
      (rectangular (SeparationInfinity.inverseExponent (fun i j=>a j i))
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)))⁻¹)) := by
  rw [fourCrossAffineUnit_signed]
  rw [mul_left_comm]
  apply congrArg (_ * ·)
  exact four_rectangle_cancellation (fun i j : I=>if i=j then 1 else 0)
    (fun i j=>(a i j:ℤ)) (fourAffine d₁ e₁ d₂ e₂)

end ElementaryPositivity.RawShuffle

end

end OAI

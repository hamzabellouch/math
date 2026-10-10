import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CanonicalCard
import OAI.Combinatorics.Chromatic.Shuffle.LaurentKernel
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentRectangularKernel
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentScalarNaturality

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance clearingTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance clearingTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance

lemma rawInverseKernel_zero (d e : I → ℕ) :
    (SeparationInfinity.rawInverseKernelUnit (fun _ _ : I=>0) d e).val=
      ∏ i,∏ x : Fin (d i),∏ y : Fin (e i),
        (affineUnit (X (Sum.inr ⟨i,y⟩)-X (Sum.inl ⟨i,x⟩) : MvPolynomial (CellVars d e) ℚ)).val := by
  have h : SeparationInfinity.rawInverseKernelUnit (fun _ _ : I=>0) d e=
      rectangular (fun i j : I=>if i=j then 1 else 0)
        (fun i j x y=>affineUnit (X (Sum.inr ⟨j,y⟩)-X (Sum.inl ⟨i,x⟩) : MvPolynomial (CellVars d e) ℚ)) := by
    simp only [SeparationInfinity.rawInverseKernelUnit,SeparationInfinity.rawFactor,
      SeparationInfinity.inverseExponent,Nat.cast_zero,sub_zero,rectangular]
  rw [h,rectangular_diagonal]
  simp only [Units.coe_prod]

lemma polynomial_crossDifference (d e : I → ℕ) :
    polynomial (relativeRaw d e (crossDifference d e))=
      crossSign d e • (SeparationInfinity.rawInverseKernelUnit (fun _ _ : I=>0) d e).val := by
  rw [relativeRaw_crossDifference,rawInverseKernel_zero]
  rw [rat_smul_series]
  simp only [map_prod,crossSign,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro y hy
  simp only [map_add,polynomial_X,polynomial_C,affineUnit_val,map_neg,map_one,neg_one_mul]
  simp only [map_sub]
  ring

lemma polynomial_crossTensor (d e : I → ℕ) :
    polynomial (relativeTaylor d e (crossTensor d e))=
      crossSign d e • (SeparationInfinity.inverseKernelUnit (fun _ _ : I=>0) d e).val := by
  apply SeparationInfinity.realize_injective d e
  rw [polynomial_map,map_relativeTaylor,tensorValue_crossTensor]
  rw [mapRing_rat_smul,
    SeparationInfinity.realize_inverseKernelUnit,polynomial_crossDifference]

omit [DecidableEq I] in
lemma crossSign_sq (d e : I → ℕ) : crossSign d e * crossSign d e=1 := by
  rw [crossSign,←Finset.prod_mul_distrib]
  simp only [←Finset.prod_mul_distrib,neg_mul_neg,one_mul,Finset.prod_const_one]

end ElementaryPositivity.RawShuffle

end

end OAI

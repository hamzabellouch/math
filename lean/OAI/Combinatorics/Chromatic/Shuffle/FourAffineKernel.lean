import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.LaurentKernel
import OAI.Combinatorics.Chromatic.Shuffle.CrossKernelExplicit
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentRectangularKernel

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def fourRelativeRaw (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ →ₐ[ℚ]
      Polynomial (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) :=
  aeval (Sum.elim (fun x=>Polynomial.C (X (Sum.inl x))+Polynomial.X)
    (fun y=>Polynomial.C (X (Sum.inr y))))

noncomputable def fourAffine (d₁ e₁ d₂ e₂ : I → ℕ)
    (i j : I) (x : Fin (d₁ i)⊕Fin (e₁ i)) (y : Fin (d₂ j)⊕Fin (e₂ j)) :=
  affineUnit (fourForwardDifference d₁ e₁ d₂ e₂ i j x y)

omit [Fintype I] [DecidableEq I] in
lemma polynomial_fourRelative_difference (d₁ e₁ d₂ e₂ : I → ℕ)
    (i j : I) (x : Fin (d₁ i)⊕Fin (e₁ i)) (y : Fin (d₂ j)⊕Fin (e₂ j)) :
    polynomial (fourRelativeRaw d₁ e₁ d₂ e₂ (fourForwardDifference d₁ e₁ d₂ e₂ i j x y))=
      (fourAffine d₁ e₁ d₂ e₂ i j x y).val := by
  simp only [fourAffine,affineUnit_val,fourForwardDifference,fourRelativeRaw,
    map_sub,aeval_X,Sum.elim_inl,Sum.elim_inr,map_add,polynomial_C,polynomial_X]
  ring

noncomputable def fourClearingUnit (d₁ e₁ d₂ e₂ : I → ℕ) :=
  rectangular (fun i j : I=>if i=j then 1 else 0) (fourAffine d₁ e₁ d₂ e₂)

noncomputable def fourTotalInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :=
  rectangular (SeparationInfinity.inverseExponent a) (fourAffine d₁ e₁ d₂ e₂)

noncomputable def fourCrossAffineUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :=
  (-1 : (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) ^ (∑ i,e₁ i*d₂ i) *
    rectangular (fun i j : I=>if i=j then 1 else 0)
      (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) *
    rectangular (fun i j : I=>if i=j then 1 else 0)
      (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) *
    rectangular (fun i j=>(a i j:ℤ))
      (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inr y)) *
    rectangular (fun i j=>(a i j:ℤ))
      (fun i j x y=>-fourAffine d₁ e₁ d₂ e₂ j i (.inr y) (.inl x))

lemma polynomial_fourRelative_cross (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    polynomial (fourRelativeRaw d₁ e₁ d₂ e₂ (fourCrossPolynomial a d₁ e₁ d₂ e₂))=
      (fourCrossAffineUnit a d₁ e₁ d₂ e₂).val := by
  rw [fourCrossPolynomial_explicit]
  simp only [map_mul,map_pow,map_neg,map_one,map_prod,polynomial_fourRelative_difference]
  unfold fourCrossAffineUnit
  rw [rectangular_diagonal,rectangular_diagonal]
  simp only [rectangular,zpow_natCast,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_neg,
    Units.val_one,Units.coe_prod]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity
open scoped TensorProduct

lemma tensor_map_projection {K A B A' B' : Type*} [CommSemiring K]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra K A] [Algebra K B] [Algebra K A'] [Algebra K B']
    (T : A →ₗ[K] B) (U : A' →ₗ[K] B') (ι : B →ₐ[K] A) (κ : B' →ₐ[K] A')
    (hT : ∀ b x,T (ι b*x)=b*T x) (hU : ∀ b x,U (κ b*x)=b*U x)
    (b : B⊗[K]B') (x : A⊗[K]A') :
    TensorProduct.map T U (Algebra.TensorProduct.map ι κ b*x)=
      b*TensorProduct.map T U x := by
  induction b using TensorProduct.inductionOn with
  | add b c hb hc => simp only [map_add,add_mul,hb,hc]
  | tmul b c =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [mul_add,map_add,hx,hy]
    | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul,Algebra.TensorProduct.tmul_mul_tmul,
        TensorProduct.map_tmul,hT,hU]

end ElementaryPositivity

end

end OAI

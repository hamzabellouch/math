import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SeparationCoefficients
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentProductNaturality
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentGeometric

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SeparatedSymmetry ElementaryPositivity.Homogeneity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma rawInverseKernel_homogeneous (a : I → I → ℕ) (d e : I → ℕ) :
    IsHomogeneous (rawInverseKernelUnit a d e).val (eulerForm a d e) := by
  classical
  have h : IsHomogeneous (rawInverseKernelUnit a d e).val
      (∑ i,∑ j,∑ _x : Fin (d i),∑ _y : Fin (e j),inverseExponent a i j) := by
    change IsHomogeneous ((Units.coeHom _) (∏ i,∏ j,∏ x : Fin (d i),∏ y : Fin (e j),rawFactor a d e i j x y)) _
    simp only [map_prod]
    apply homogeneous_prod
    intro i hi
    apply homogeneous_prod
    intro j hj
    apply homogeneous_prod
    intro x hx
    apply homogeneous_prod
    intro y hy
    exact homogeneous_affine_zpow _
      ((isWeightedHomogeneous_X ℚ (fun _=>(1:ℤ)) _).sub
        (isWeightedHomogeneous_X ℚ (fun _=>(1:ℤ)) _)) _
  have he : (∑ i,∑ j,∑ _x : Fin (d i),∑ _y : Fin (e j),inverseExponent a i j)=eulerForm a d e := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold eulerForm
    rw [← ElementaryPositivity.inverseEuler_exponent a d e]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold inverseExponent
    ring
  rwa [he] at h
omit [Fintype I] [DecidableEq I] in
lemma relativeRaw_homogeneous (d e : I → ℕ) (f : MvPolynomial (CellVars d e) ℚ)
    (ℓ : ℤ) (hf : f.IsWeightedHomogeneous (fun _=>(1:ℤ)) ℓ) :
    IsHomogeneous (polynomial (relativeRaw d e f)) ℓ := by
  apply homogeneous_ringHom (polynomial.comp (relativeRaw d e).toRingHom) _ _ f ℓ hf
  · intro q
    show IsHomogeneous (polynomial (relativeRaw d e (MvPolynomial.C q))) 0
    rw [show relativeRaw d e (MvPolynomial.C q)=Polynomial.C (MvPolynomial.C q) by simp [relativeRaw],polynomial_C]
    change IsHomogeneous (single 0 (MvPolynomial.C q)) 0
    simpa only [sub_zero] using homogeneous_single 0 0 (MvPolynomial.C q) (isWeightedHomogeneous_C _ _)
  · intro v
    rcases v with (v|v)
    · show IsHomogeneous (polynomial (relativeRaw d e (X (Sum.inl v)))) 1
      rw [show relativeRaw d e (X (Sum.inl v))=Polynomial.C (X (Sum.inl v))+Polynomial.X by simp [relativeRaw]]
      rw [map_add,polynomial_C,polynomial_X,zUnit_val]
      apply LaurentAtInfinity.IsHomogeneous.add
      · change IsHomogeneous (single 0 (X (Sum.inl v))) 1
        simpa only [sub_zero] using homogeneous_single 0 1 (X (Sum.inl v)) (isWeightedHomogeneous_X ℚ _ _)
      · simpa using homogeneous_single (-1) 0 (1 : MvPolynomial (CellVars d e) ℚ) (isWeightedHomogeneous_one _ _)
    · show IsHomogeneous (polynomial (relativeRaw d e (X (Sum.inr v)))) 1
      rw [show relativeRaw d e (X (Sum.inr v))=Polynomial.C (X (Sum.inr v)) by simp [relativeRaw]]
      rw [polynomial_C]
      change IsHomogeneous (single 0 (X (Sum.inr v))) 1
      simpa only [sub_zero] using homogeneous_single 0 1 (X (Sum.inr v)) (isWeightedHomogeneous_X ℚ _ _)
noncomputable def rawSeparationSeries (a : I → I → ℕ) (d e : I → ℕ) (f : S (d+e)) :
    LaurentSeries (MvPolynomial (CellVars d e) ℚ) :=
  (rawInverseKernelUnit a d e).val * polynomial (relativeRaw d e (rename (cutSplit (firstCut d e)).symm f.val))
lemma rawSeparationSeries_homogeneous (a : I → I → ℕ) (d e : I → ℕ)
    (f : S (d+e)) (ℓ : ℤ) (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) ℓ) :
    IsHomogeneous (rawSeparationSeries a d e f) (ℓ+eulerForm a d e) := by
  have h:=(rawInverseKernel_homogeneous a d e).mul
    (relativeRaw_homogeneous d e _ ℓ (constantWeight_rename (cutSplit (firstCut d e)).symm f.val hf))
  simpa only [rawSeparationSeries,add_comm] using h
end ElementaryPositivity.RawShuffle.SeparationInfinity

end
section
namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SeparatedSymmetry ElementaryPositivity.Homogeneity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable def tensorSeparationSeries (a : I → I → ℕ) (d e : I → ℕ) (f : S (d+e)) :
    LaurentSeries (S d ⊗[ℚ] S e) :=
  (inverseKernelUnit a d e).val * polynomial (R:=S d ⊗[ℚ] S e) (relativeTaylor d e (restrictTensor (firstCut d e) f))
lemma realize_tensorSeparationSeries (a : I → I → ℕ) (d e : I → ℕ) (f : S (d+e)) :
    mapRing (R:=S d ⊗[ℚ] S e) (S:=MvPolynomial (CellVars d e) ℚ) (tensorValueAlg d e).toRingHom (tensorSeparationSeries a d e f)=rawSeparationSeries a d e f := by
  rw [tensorSeparationSeries,mapRing_mul_polynomial,realize_inverseKernelUnit,
    map_relativeTaylor,tensorValue_restrictTensor]
  rfl
lemma tensorSeparationSeries_coeff (a : I → I → ℕ) (d e : I → ℕ) (f : S (d+e)) (k : ℤ) :
    (tensorSeparationSeries a d e f).coeff k=
      separateTensor d e ((rawSeparationSeries a d e f).coeff k) := by
  rw [← realize_tensorSeparationSeries,mapRing_coeff]
  exact (separateTensor_tensorValue d e _).symm
lemma separationSeries_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (f : S (d+e)) :
    separationSeries a c η hc hs (quotientAlg a (SlopeArithmetic.slope c η) (d+e) f)=
      mapRing (R:=S d ⊗[ℚ] S e) (S:=B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) (quotientTensor a (SlopeArithmetic.slope c η) d e).toRingHom (tensorSeparationSeries a d e f) := by
  rw [tensorSeparationSeries,mapRing_mul_polynomial]
  dsimp only [separationSeries,LinearMap.comp_apply,AlgHom.toLinearMap_apply]
  rw [restrictionRelativeB_mk]
  rfl

lemma separationCoefficient_mk_raw (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (f : S (d+e)) (j : ℤ) :
    separationCoefficient a c η hc hs j (quotientAlg a (SlopeArithmetic.slope c η) (d+e) f)=
      quotientTensor a (SlopeArithmetic.slope c η) d e
        (separateTensor d e ((rawSeparationSeries a d e f).coeff (-j))) := by
  change (separationSeries a c η hc hs (quotientAlg a (SlopeArithmetic.slope c η) (d+e) f)).coeff (-j)=_
  rw [separationSeries_mk,mapRing_coeff,tensorSeparationSeries_coeff]
  rfl

theorem separationCoefficient_originalDegree (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (f : S (d+e)) (ℓ j m n : ℤ) (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) ℓ)
    (hmn : m+n≠ℓ+eulerForm a d e-j) :
    TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d m)
      (componentB a (SlopeArithmetic.slope c η) e n)
      (separationCoefficient a c η hc hs j (quotientAlg a (SlopeArithmetic.slope c η) (d+e) f))=0 := by
  rw [separationCoefficient_mk_raw,component_quotientTensor]
  have h:=rawSeparationSeries_homogeneous a d e f ℓ hf (-j)
  rw [component_separateTensor_homogeneous d e _ _ h m n (by simpa only [sub_eq_add_neg] using hmn),map_zero]

theorem separationCoefficient_aboveDegree (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (f : S (d+e)) (ℓ j : ℤ) (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) ℓ)
    (hj : ℓ+eulerForm a d e<j) :
    separationCoefficient a c η hc hs j (quotientAlg a (SlopeArithmetic.slope c η) (d+e) f)=0 := by
  rw [separationCoefficient_mk_raw,
    homogeneous_negative_eq_zero _ (rawSeparationSeries_homogeneous a d e f ℓ hf (-j)) (by omega),map_zero,map_zero]
end ElementaryPositivity.RawShuffle.SeparationInfinity

end

end OAI

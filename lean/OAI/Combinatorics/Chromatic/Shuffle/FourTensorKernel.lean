import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.ShuffleProjection
import OAI.Combinatorics.Chromatic.Shuffle.FourColumns
import OAI.Combinatorics.Chromatic.Shuffle.FourKernelCancellation

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance kernelTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance kernelTensorDistrib (d e : I → ℕ) :
    DistribSMul (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) where
  smul_add := mul_add
noncomputable local instance kernelTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance kernelFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance kernelFourAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

noncomputable local instance kernelTensorSelf (d e : I → ℕ) :
    Module (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) := Semiring.toModule
noncomputable local instance kernelTensorNonUnital (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (kernelTensorRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance kernelFourNonUnital (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (kernelFourRing d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring

lemma realize_inverseKernelUnit_unit (a : I → I → ℕ) (d e : I → ℕ) :
    Units.map (mapRing (tensorValueAlg d e).toRingHom).toMonoidHom
      (SeparationInfinity.inverseKernelUnit a d e)=SeparationInfinity.rawInverseKernelUnit a d e := by
  apply Units.ext
  exact SeparationInfinity.realize_inverseKernelUnit a d e

lemma fourKernel_lift_naturality (a : I → I → ℕ) (d e d₁ e₁ d₂ e₂ : I → ℕ)
    (F : S d⊗[ℚ]S e →ₐ[ℚ] (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))
    (r : CellVars d e → CellVars d₁ e₁⊕CellVars d₂ e₂)
    (h : ∀ x,fourValueAlg d₁ e₁ d₂ e₂ (F x)=rename r (tensorValue d e x)) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S d⊗[ℚ]S e) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) F.toRingHom).toMonoidHom (SeparationInfinity.inverseKernelUnit a d e))=
    Units.map (mapRing (rename r).toRingHom).toMonoidHom (SeparationInfinity.rawInverseKernelUnit a d e) := by
  apply Units.ext
  apply HahnSeries.ext
  funext k
  change fourValueAlg d₁ e₁ d₂ e₂ (F ((SeparationInfinity.inverseKernelUnit a d e).val.coeff k))=
    rename r ((SeparationInfinity.rawInverseKernelUnit a d e).val.coeff k)
  rw [h]
  have hr := congrArg (fun x : LaurentSeries (MvPolynomial (CellVars d e) ℚ)=>x.coeff k)
    (SeparationInfinity.realize_inverseKernelUnit a d e)
  exact congrArg (rename r) hr

lemma fourKernel_restrictRows (a : I → I → ℕ) {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S (d₁+e₁)⊗[ℚ]S (d₂+e₂)) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (restrictRows d₁ e₁ d₂ e₂ A B).toRingHom).toMonoidHom
        (SeparationInfinity.inverseKernelUnit a (d₁+e₁) (d₂+e₂)))=
      fourTotalInverseUnit a d₁ e₁ d₂ e₂ := by
  rw [fourKernel_lift_naturality a _ _ _ _ _ _ _ _ (fourValue_restrictRows A B)]
  exact rowSplit_inverseKernel a A B

lemma fourKernel_firstColumn (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S d₁⊗[ℚ]S d₂) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
        (SeparationInfinity.inverseKernelUnit a d₁ d₂))=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) := by
  refine Eq.trans (fourKernel_lift_naturality a d₁ d₂ d₁ e₁ d₂ e₂
    ( firstColumnAlg d₁ e₁ d₂ e₂ ) _ (fourValue_firstColumn d₁ e₁ d₂ e₂)) ?_
  have he : firstColumnVars d₁ e₁ d₂ e₂ =
      Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl) := by
    funext x; cases x <;> rfl
  rw [he]
  have h := rawKernel_rename (σ:=CellVars d₁ e₁⊕CellVars d₂ e₂) a d₁ d₂
    (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl)
  simpa only [fourAffine,fourForwardDifference,Function.comp_apply,
    Equiv.sigmaSumDistrib_apply,Sum.map_inl,Sum.map_inr,firstColumnVars,secondColumnVars,crossingColumnVars] using h

lemma fourKernel_secondColumn (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S e₁⊗[ℚ]S e₂) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
        (SeparationInfinity.inverseKernelUnit a e₁ e₂))=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) := by
  refine Eq.trans (fourKernel_lift_naturality a e₁ e₂ d₁ e₁ d₂ e₂
    ( secondColumnAlg d₁ e₁ d₂ e₂ ) _ (fourValue_secondColumn d₁ e₁ d₂ e₂)) ?_
  have he : secondColumnVars d₁ e₁ d₂ e₂ =
      Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr) := by
    funext x; cases x <;> rfl
  rw [he]
  have h := rawKernel_rename (σ:=CellVars d₁ e₁⊕CellVars d₂ e₂) a e₁ e₂
    (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr)
  simpa only [fourAffine,fourForwardDifference,Function.comp_apply,
    Equiv.sigmaSumDistrib_apply,Sum.map_inl,Sum.map_inr,firstColumnVars,secondColumnVars,crossingColumnVars] using h

lemma fourKernel_crossingColumn (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S e₁⊗[ℚ]S d₂) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (crossingColumnAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
        (SeparationInfinity.inverseKernelUnit a e₁ d₂))=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)) := by
  refine Eq.trans (fourKernel_lift_naturality a e₁ d₂ d₁ e₁ d₂ e₂
    ( crossingColumnAlg d₁ e₁ d₂ e₂ ) _ (fourValue_crossingColumn d₁ e₁ d₂ e₂)) ?_
  have h := rawKernel_rename (σ:=CellVars d₁ e₁⊕CellVars d₂ e₂) a e₁ d₂
    (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inl)
  simpa only [fourAffine,fourForwardDifference,Function.comp_apply,
    Equiv.sigmaSumDistrib_apply,Sum.map_inl,Sum.map_inr,firstColumnVars,secondColumnVars,crossingColumnVars] using h

lemma fourTensor_cross_realize (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom
      (polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)))=
      (fourCrossAffineUnit a d₁ e₁ d₂ e₂).val := by
  rw [polynomial_map,map_fourRelativeTaylor,fourValue_fourCrossTensor,polynomial_fourRelative_cross]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance cancelTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance cancelTensorDistrib (d e : I → ℕ) :
    DistribSMul (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) where
  smul_add := mul_add
noncomputable local instance cancelTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance cancelFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance cancelFourAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

noncomputable def mappedInverseKernel {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : I → I → ℕ) (d e : I → ℕ) (f : S d⊗[ℚ]S e →ₐ[ℚ] R) : (LaurentSeries R)ˣ :=
  Units.map (mapRing f.toRingHom).toMonoidHom (SeparationInfinity.inverseKernelUnit a d e)

noncomputable local instance cancelTensorSelf (d e : I → ℕ) :
    Module (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) := Semiring.toModule
noncomputable local instance cancelTensorNonUnital (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (cancelTensorRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance cancelFourNonUnital (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (cancelFourRing d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring

noncomputable local instance cancelSeriesRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) := inferInstance

noncomputable def fourRowsInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) : (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  mappedInverseKernel a (d₁+e₁) (d₂+e₂) (restrictRows d₁ e₁ d₂ e₂ A B)

noncomputable def fourFirstInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  mappedInverseKernel a d₁ d₂ (firstColumnAlg d₁ e₁ d₂ e₂)

noncomputable def fourSecondInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  mappedInverseKernel a e₁ e₂ (secondColumnAlg d₁ e₁ d₂ e₂)

noncomputable def fourCrossingInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  mappedInverseKernel a e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂)

lemma fourTotalInverseUnit_zero (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourTotalInverseUnit (fun _ _ : I=>0) d₁ e₁ d₂ e₂=fourClearingUnit d₁ e₁ d₂ e₂ := by
  unfold fourTotalInverseUnit fourClearingUnit
  congr 1
  funext i j
  simp only [SeparationInfinity.inverseExponent,Nat.cast_zero,sub_zero]

noncomputable def fourSeriesValue (d₁ e₁ d₂ e₂ : I → ℕ) :
    LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) →+*
      LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) :=
  mapRing (fourValueAlg d₁ e₁ d₂ e₂).toRingHom

lemma fourSeriesValue_injective (d₁ e₁ d₂ e₂ : I → ℕ) :
    Function.Injective (fourSeriesValue d₁ e₁ d₂ e₂) :=
  mapRing_injective (fourValueAlg d₁ e₁ d₂ e₂).toRingHom (fourValue_injective d₁ e₁ d₂ e₂)

lemma fourSeriesValue_rows (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B)=
      fourTotalInverseUnit a d₁ e₁ d₂ e₂ := fourKernel_restrictRows a A B

lemma fourSeriesValue_first (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourFirstInverseUnit a d₁ e₁ d₂ e₂)=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) :=
  fourKernel_firstColumn a d₁ e₁ d₂ e₂

lemma fourSeriesValue_second (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourSecondInverseUnit a d₁ e₁ d₂ e₂)=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) :=
  fourKernel_secondColumn a d₁ e₁ d₂ e₂

lemma fourSeriesValue_crossing (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourCrossingInverseUnit a d₁ e₁ d₂ e₂)=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)) :=
  fourKernel_crossingColumn a d₁ e₁ d₂ e₂

lemma fourSeriesValue_cross (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourSeriesValue d₁ e₁ d₂ e₂
      (polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)))=
      (fourCrossAffineUnit a d₁ e₁ d₂ e₂).val := fourTensor_cross_realize a d₁ e₁ d₂ e₂

lemma units_map_neg_one {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Units.map f.toMonoidHom (-1 : Rˣ)=(-1 : Sˣ) := by
  apply Units.ext
  change f (-1) = -1
  rw [map_neg,map_one]

lemma ring_map_unit_val {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (u : Rˣ) :
    f u.val = (Units.map f.toMonoidHom u).val := rfl

lemma ring_map_inv_unit_val {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (u : Rˣ) :
    f (u⁻¹).val = ((Units.map f.toMonoidHom u)⁻¹).val := rfl

lemma ring_map_signedUnits {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B C D : Rˣ) (w : ℤ) :
    f (((-1)^w*(A*B*(C*D⁻¹))).val)=
    ((-1)^w*(Units.map f.toMonoidHom A*Units.map f.toMonoidHom B*
      (Units.map f.toMonoidHom C*(Units.map f.toMonoidHom D)⁻¹))).val := by
  rw [ring_map_unit_val]
  simp only [map_mul,map_inv,map_zpow,units_map_neg_one]

lemma unitKernelCancellation_lift {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f)
    (K L A B C D : Rˣ) (P : R) (k l a b c d p : Sˣ)
    (hK : Units.map f.toMonoidHom K=k) (hL : Units.map f.toMonoidHom L=l)
    (hA : Units.map f.toMonoidHom A=a) (hB : Units.map f.toMonoidHom B=b)
    (hC : Units.map f.toMonoidHom C=c) (hD : Units.map f.toMonoidHom D=d)
    (hP : f P=p.val) (w : ℤ)
    (h : k*l⁻¹*p=(-1)^w*(a*b*(c*d⁻¹))) :
    K.val*(L⁻¹).val*P=((-1)^w*(A*B*(C*D⁻¹))).val := by
  apply hf
  rw [map_mul,map_mul,hP]
  simp only [ring_map_unit_val,map_mul,map_inv,map_zpow,units_map_neg_one,hK,hL,hA,hB,hC,hD]
  exact congrArg Units.val h

lemma unitKernelCancellation_lift2 {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f)
    (K L A B C D : Rˣ) (P : R) (p : Sˣ) (hP : f P=p.val) (w : ℤ)
    (h : Units.map f.toMonoidHom K*(Units.map f.toMonoidHom L)⁻¹*p=
      (-1)^w*(Units.map f.toMonoidHom A*Units.map f.toMonoidHom B*
      (Units.map f.toMonoidHom C*(Units.map f.toMonoidHom D)⁻¹))) :
    K.val*(L⁻¹).val*P=((-1)^w*(A*B*(C*D⁻¹))).val :=
  unitKernelCancellation_lift f hf K L A B C D P _ _ _ _ _ _ p rfl rfl rfl rfl rfl rfl hP w h

lemma fourSeriesValue_rows_val (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    fourSeriesValue d₁ e₁ d₂ e₂ (fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B).val=
      (fourTotalInverseUnit a d₁ e₁ d₂ e₂).val :=
  congrArg Units.val (fourSeriesValue_rows a d₁ e₁ d₂ e₂ A B)

lemma fourSeriesValue_rows_inv_val (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    fourSeriesValue d₁ e₁ d₂ e₂ ((fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B)⁻¹).val=
      ((fourTotalInverseUnit a d₁ e₁ d₂ e₂)⁻¹).val :=
  congrArg (fun u=> (u⁻¹).val) (fourSeriesValue_rows a d₁ e₁ d₂ e₂ A B)

noncomputable def fourTensorKernelRHS (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  (-1)^eulerForm a d₂ e₁ *
    (fourFirstInverseUnit a d₁ e₁ d₂ e₂ * fourSecondInverseUnit a d₁ e₁ d₂ e₂ *
      (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹))

lemma fourSeriesValue_kernelRHS (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom
      (fourTensorKernelRHS a d₁ e₁ d₂ e₂)=
    fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
      fourCrossAffineUnit a d₁ e₁ d₂ e₂ := by
  apply Units.ext
  change fourSeriesValue d₁ e₁ d₂ e₂ (fourTensorKernelRHS a d₁ e₁ d₂ e₂).val = _
  unfold fourTensorKernelRHS
  rw [ring_map_signedUnits]
  apply congrArg Units.val
  refine Eq.trans ?_ (fourKernel_cancellation a d₁ e₁ d₂ e₂).symm
  apply congrArg ((-1)^eulerForm a d₂ e₁ * ·)
  exact congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (fourSeriesValue_first a d₁ e₁ d₂ e₂)
      (fourSeriesValue_second a d₁ e₁ d₂ e₂))
    (congrArg₂ (· * ·) (fourSeriesValue_crossing a d₁ e₁ d₂ e₂)
      (congrArg Inv.inv (fourSeriesValue_crossing (fun i j=>a j i) d₁ e₁ d₂ e₂)))

lemma fourSeriesValue_kernelRHS_val (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourSeriesValue d₁ e₁ d₂ e₂ (fourTensorKernelRHS a d₁ e₁ d₂ e₂).val=
    (fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
      fourCrossAffineUnit a d₁ e₁ d₂ e₂).val :=
  congrArg Units.val (fourSeriesValue_kernelRHS a d₁ e₁ d₂ e₂)

lemma fourSeriesValue_kernelLHS (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    fourSeriesValue d₁ e₁ d₂ e₂
      ((fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B).val *
        ((fourRowsInverseUnit (fun _ _ : I=>0) d₁ e₁ d₂ e₂ A B)⁻¹).val *
        polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)))=
    (fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
      fourCrossAffineUnit a d₁ e₁ d₂ e₂).val := by
  rw [(fourSeriesValue d₁ e₁ d₂ e₂).map_mul,(fourSeriesValue d₁ e₁ d₂ e₂).map_mul,
    fourSeriesValue_rows_val,fourSeriesValue_rows_inv_val,fourTotalInverseUnit_zero,fourSeriesValue_cross]
  rfl

lemma fourTensorKernel_cancellation (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    (fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B).val *
      ((fourRowsInverseUnit (fun _ _ : I=>0) d₁ e₁ d₂ e₂ A B)⁻¹).val *
      polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂))=
    (((-1 : (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ)^eulerForm a d₂ e₁) *
      (fourFirstInverseUnit a d₁ e₁ d₂ e₂ *
        fourSecondInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹))).val := by
  apply fourSeriesValue_injective d₁ e₁ d₂ e₂
  exact (fourSeriesValue_kernelLHS a d₁ e₁ d₂ e₂ A B).trans
    (fourSeriesValue_kernelRHS_val a d₁ e₁ d₂ e₂).symm

end ElementaryPositivity.RawShuffle

end

end OAI

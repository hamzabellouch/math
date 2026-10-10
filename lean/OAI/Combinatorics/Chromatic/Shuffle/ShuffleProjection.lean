import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.FourAffineKernel
import OAI.Combinatorics.Chromatic.Walls.LaurentProjectionFormula

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open ElementaryPositivity.LaurentAtInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance projectionTensorSCommRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance projectionTensorSAlgebra (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance

noncomputable local instance projectionFourSCommRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance projectionFourSAlgebra (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

noncomputable local instance projectionTensorSNonUnitalNonAssocSemiring (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (projectionTensorSCommRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance projectionFourSNonUnitalNonAssocSemiring (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (projectionFourSCommRing d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring

lemma shuffleTensor_projection (a : I → I → ℕ) {d e : I → ℕ}
    (A : Cut d e) (f : S (d+e)) (x : S d⊗[ℚ]S e) :
    shuffleTensorLinear a d e (restrictTensorAlg A f*x)=
      f*shuffleTensorLinear a d e x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [mul_add,map_add,hx,hy]
  | tmul x y =>
    apply localizeS_injective
    rw [←tensorShuffle_tensorValue,tensorValue_mul]
    change tensorShuffle a (tensorValue d e (restrictTensor A f)*tensorValue d e (x⊗ₜ[ℚ]y))=_
    rw [tensorValue_restrictTensor,tensorValue_tmul,tensorShuffle_restricted_mul]
    rw [←shufflePolynomial_eq,shuffleTensorLinear_tmul]
    exact (map_mul (algebraMap (MvPolynomial (Σi,Fin (d i+e i)) ℚ)
      (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))) f.val (shufflePolynomial a x y).val).symm

noncomputable def restrictRows (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    S (d₁+e₁)⊗[ℚ]S (d₂+e₂) →ₐ[ℚ] (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂) :=
  Algebra.TensorProduct.map (restrictTensorAlg A) (restrictTensorAlg B)

lemma twoTarget_projection (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂)
    (f : S (d₁+e₁)⊗[ℚ]S (d₂+e₂))
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    twoTargetTransfer a d₁ e₁ d₂ e₂ (restrictRows d₁ e₁ d₂ e₂ A B f*x)=
      f*twoTargetTransfer a d₁ e₁ d₂ e₂ x :=
  tensor_map_projection _ _ _ _ (shuffleTensor_projection a A) (shuffleTensor_projection a B) f x

lemma twoTarget_Laurent_projection (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂)
    (f : LaurentSeries (S (d₁+e₁)⊗[ℚ]S (d₂+e₂)))
    (x : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) :
    mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂)
      (mapRing (restrictRows d₁ e₁ d₂ e₂ A B).toRingHom f*x)=
      f*mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) x :=
  mapLinear_projection _ _ (twoTarget_projection a d₁ e₁ d₂ e₂ A B) f x

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance rowTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance rowTensorAlgebra (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance rowFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance rowFourAlgebra (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

omit [Fintype I] [DecidableEq I] in
lemma cutSplit_pack {d e : I → ℕ} (A : Cut d e) (i : I)
    (x : Fin (d i)⊕Fin (e i)) :
    (cutSplit A).symm ⟨i,packSplit A i x⟩=(Equiv.sigmaSumDistrib _ _) ⟨i,x⟩ := by
  apply (cutSplit A).injective
  rw [Equiv.apply_symm_apply]
  cases x <;> rfl

noncomputable def rowSplitEquiv {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    CellVars (d₁+e₁) (d₂+e₂) ≃ CellVars d₁ e₁⊕CellVars d₂ e₂ :=
  Equiv.sumCongr (cutSplit A).symm (cutSplit B).symm

omit [Fintype I] in
lemma rowSplit_rawFactor (a : I → I → ℕ) {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) (i j : I)
    (x : Fin (d₁ i)⊕Fin (e₁ i)) (y : Fin (d₂ j)⊕Fin (e₂ j)) :
    Units.map (mapRing (rename (rowSplitEquiv A B)).toRingHom).toMonoidHom
      (SeparationInfinity.rawFactor a (d₁+e₁) (d₂+e₂) i j (packSplit A i x) (packSplit B j y))=
      fourAffine d₁ e₁ d₂ e₂ i j x y ^ SeparationInfinity.inverseExponent a i j := by
  unfold SeparationInfinity.rawFactor
  rw [map_zpow,affineUnit_map]
  congr 2
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,map_sub,rename_X,rowSplitEquiv,
    Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,cutSplit_pack]
  rfl

lemma rowSplit_inverseKernel (a : I → I → ℕ) {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    Units.map (mapRing (rename (rowSplitEquiv A B)).toRingHom).toMonoidHom
      (SeparationInfinity.rawInverseKernelUnit a (d₁+e₁) (d₂+e₂))=
      fourTotalInverseUnit a d₁ e₁ d₂ e₂ := by
  simp only [SeparationInfinity.rawInverseKernelUnit,map_prod,fourTotalInverseUnit,rectangular]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  calc
    _ = ∏ x : Fin (d₁ i)⊕Fin (e₁ i), ∏ y : Fin (d₂ j+e₂ j),
        Units.map (mapRing (rename (rowSplitEquiv A B)).toRingHom).toMonoidHom
          (SeparationInfinity.rawFactor a (d₁+e₁) (d₂+e₂) i j (packSplit A i x) y) :=
      (Equiv.prod_comp (packSplit A i) _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro x hx
      calc
        _ = ∏ y : Fin (d₂ j)⊕Fin (e₂ j),
            Units.map (mapRing (rename (rowSplitEquiv A B)).toRingHom).toMonoidHom
              (SeparationInfinity.rawFactor a (d₁+e₁) (d₂+e₂) i j (packSplit A i x) (packSplit B j y)) :=
          (Equiv.prod_comp (packSplit B j) _).symm
        _ = _ := Finset.prod_congr rfl (fun y hy=>rowSplit_rawFactor a A B i j x y)

lemma fourValue_restrictRows {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) (x : S (d₁+e₁)⊗[ℚ]S (d₂+e₂)) :
    fourValue d₁ e₁ d₂ e₂ (restrictRows d₁ e₁ d₂ e₂ A B x)=
      rename (rowSplitEquiv A B) (tensorValue (d₁+e₁) (d₂+e₂) x) := by
  change fourValue d₁ e₁ d₂ e₂ (TensorProduct.map (restrictTensor A) (restrictTensor B) x)=_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    change fourValue d₁ e₁ d₂ e₂ (restrictTensor A x⊗ₜ[ℚ]restrictTensor B y)=_
    rw [fourValue_tmul,tensorValue_restrictTensor,tensorValue_restrictTensor,tensorValue_tmul]
    simp only [map_mul,rename_rename]
    rfl

end ElementaryPositivity.RawShuffle

end

end OAI

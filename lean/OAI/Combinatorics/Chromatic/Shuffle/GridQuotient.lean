import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNExpansion
import OAI.Combinatorics.Chromatic.Shuffle.Restriction

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] tensorSCommRing tensorSAlgebra fourSCommRing fourSAlgebra
noncomputable local instance tensorBCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d ⊗[ℚ] B a μ e) := inferInstance
noncomputable local instance tensorBAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d ⊗[ℚ] B a μ e) := inferInstance

noncomputable local instance fourBCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := inferInstance
noncomputable local instance fourBAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := inferInstance

noncomputable local instance tensorBNonUnitalNonAssocSemiring (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) := (tensorBCommRing a μ d e).toNonUnitalNonAssocSemiring
noncomputable local instance fourBNonUnitalNonAssocSemiring (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) :=
  (fourBCommRing a μ d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring

noncomputable def shuffleTensorBUnit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) d⊗[ℚ]B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) :=
  TensorProduct.lift (shuffleBUnit a c η hc d e hs)

lemma quotient_shuffleTensorUnit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (x : S d⊗[ℚ]S e) :
    quotientAlg a (slope c η) (d+e) (shuffleTensorLinear a d e x)=
    shuffleTensorBUnit a c η hc d e hs (quotientTensor a (slope c η) d e x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => rfl

noncomputable def fourQuotient (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂) →ₐ[ℚ]
    (B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  Algebra.TensorProduct.map (quotientTensor a μ d₁ e₁) (quotientTensor a μ d₂ e₂)

noncomputable def fourInterchangeB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (B a μ d₁⊗[ℚ]B a μ d₂)⊗[ℚ](B a μ e₁⊗[ℚ]B a μ e₂) ≃ₗ[ℚ]
    (B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  TensorProduct.tensorTensorTensorComm ℚ _ _ _ _

lemma fourQuotient_interchange (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁⊗[ℚ]S d₂) (g : S e₁⊗[ℚ]S e₂) :
    (fourQuotient a μ d₁ e₁ d₂ e₂).toLinearMap (fourInterchange d₁ e₁ d₂ e₂ (f⊗ₜ[ℚ]g))=
    fourInterchangeB a μ d₁ e₁ d₂ e₂
      (quotientTensor a μ d₁ d₂ f⊗ₜ[ℚ]quotientTensor a μ e₁ e₂ g) := by
  exact (LinearMap.congr_fun (TensorProduct.tensorTensorTensorComm_comp_map ℚ
    (quotientAlg a μ d₁).toLinearMap (quotientAlg a μ d₂).toLinearMap
    (quotientAlg a μ e₁).toLinearMap (quotientAlg a μ e₂).toLinearMap) (f⊗ₜ[ℚ]g)).symm

lemma quotient_twoTargetTransfer_unit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ x)=
    TensorProduct.map (shuffleTensorBUnit a c η hc d₁ e₁ h₁) (shuffleTensorBUnit a c η hc d₂ e₂ h₂)
      ((fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toLinearMap x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    change (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)).toLinearMap
      ((twoTargetTransfer a d₁ e₁ d₂ e₂) (x+y))=_
    rw [(twoTargetTransfer a d₁ e₁ d₂ e₂).map_add,LinearMap.map_add,LinearMap.map_add,LinearMap.map_add]
    exact congrArg₂ (·+·) hx hy
  | tmul x y =>
    change quotientAlg a (slope c η) (d₁+e₁) (shuffleTensorLinear a d₁ e₁ x)⊗ₜ[ℚ]
      quotientAlg a (slope c η) (d₂+e₂) (shuffleTensorLinear a d₂ e₂ y)=_
    rw [quotient_shuffleTensorUnit a c η hc d₁ e₁ h₁,
      quotient_shuffleTensorUnit a c η hc d₂ e₂ h₂]
    rfl

lemma fourQuotient_grid_factor (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (A : Cut d₁ d₂) (C : Cut e₁ e₂) (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toLinearMap
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))=
    fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂
      (restrictionBUnit a c η hc hd A (quotientAlg a (slope c η) (d₁+d₂) f)⊗ₜ[ℚ]
       restrictionBUnit a c η hc he C (quotientAlg a (slope c η) (e₁+e₂) g)) *
    (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toLinearMap (fourCrossTensor a d₁ e₁ d₂ e₂) := by
  rw [separateFour_grid_factor a d₁ e₁ d₂ e₂ A C]
  change (fourQuotient a (slope c η) d₁ e₁ d₂ e₂) (_ * _)=_
  rw [map_mul]
  change (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toLinearMap _ * _=_
  rw [fourQuotient_interchange]
  rfl

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.TensorColumns
open scoped TensorProduct
variable {K A B C D : Type*} [CommRing K]
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K D]

noncomputable def first : A⊗[K]B →ₐ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeLeft
noncomputable def second : C⊗[K]D →ₐ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight

lemma first_tmul (a : A) (b : B) :
    first (C:=C) (D:=D) (a⊗ₜ[K]b)=(a⊗ₜ[K]1)⊗ₜ[K](b⊗ₜ[K]1) := rfl
lemma second_tmul (c : C) (d : D) :
    second (A:=A) (B:=B) (c⊗ₜ[K]d)=(1⊗ₜ[K]c)⊗ₜ[K](1⊗ₜ[K]d) := rfl

lemma product (x : A⊗[K]B) (y : C⊗[K]D) :
    first x * second y=TensorProduct.tensorTensorTensorComm K A B C D (x⊗ₜ[K]y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => rw [map_add,add_mul,TensorProduct.add_tmul,(TensorProduct.tensorTensorTensorComm K A B C D).map_add,hx,hz]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add,mul_add,TensorProduct.tmul_add,(TensorProduct.tensorTensorTensorComm K A B C D).map_add,hy,hz]
    | tmul c d =>
      rw [first_tmul,second_tmul,TensorProduct.tensorTensorTensorComm_tmul]
      simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

end ElementaryPositivity.TensorColumns

end

end OAI

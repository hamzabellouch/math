import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.BothTaylorB
import OAI.Combinatorics.Chromatic.Shuffle.FourAffineKernel

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance columnTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance columnTensorAlgebra (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance columnFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance columnFourAlgebra (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

noncomputable def firstColumnAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    S d₁⊗[ℚ] S d₂ →ₐ[ℚ] (S d₁⊗[ℚ] S e₁)⊗[ℚ](S d₂⊗[ℚ] S e₂) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeLeft

noncomputable def secondColumnAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    S e₁⊗[ℚ] S e₂ →ₐ[ℚ] (S d₁⊗[ℚ] S e₁)⊗[ℚ](S d₂⊗[ℚ] S e₂) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight

noncomputable def crossingColumnAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    S e₁⊗[ℚ] S d₂ →ₐ[ℚ] (S d₁⊗[ℚ] S e₁)⊗[ℚ](S d₂⊗[ℚ] S e₂) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeLeft

def crossingColumnVars (d₁ e₁ d₂ e₂ : I → ℕ) :
    CellVars e₁ d₂ → CellVars d₁ e₁⊕CellVars d₂ e₂ :=
  Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inl)

omit [Fintype I] [DecidableEq I] in
lemma fourValue_firstColumn (d₁ e₁ d₂ e₂ : I → ℕ) (x : S d₁⊗[ℚ]S d₂) :
    fourValueAlg d₁ e₁ d₂ e₂ (firstColumnAlg d₁ e₁ d₂ e₂ x)=
      rename (firstColumnVars d₁ e₁ d₂ e₂) (tensorValue d₁ d₂ x) := by
  have h : ((fourValueAlg d₁ e₁ d₂ e₂).comp (firstColumnAlg d₁ e₁ d₂ e₂)).toLinearMap=
      ((rename (firstColumnVars d₁ e₁ d₂ e₂)).comp (tensorValueAlg d₁ d₂)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change fourValue d₁ e₁ d₂ e₂ ((u⊗ₜ[ℚ]1)⊗ₜ[ℚ](v⊗ₜ[ℚ]1))=
      rename (firstColumnVars d₁ e₁ d₂ e₂) (tensorValue d₁ d₂ (u⊗ₜ[ℚ]v))
    simp only [fourValue_tmul,tensorValue_tmul,OneMemClass.coe_one,map_one,mul_one,
      map_mul,rename_rename]
    rfl
  exact LinearMap.congr_fun h x

omit [Fintype I] [DecidableEq I] in
lemma fourValue_secondColumn (d₁ e₁ d₂ e₂ : I → ℕ) (x : S e₁⊗[ℚ]S e₂) :
    fourValueAlg d₁ e₁ d₂ e₂ (secondColumnAlg d₁ e₁ d₂ e₂ x)=
      rename (secondColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ e₂ x) := by
  have h : ((fourValueAlg d₁ e₁ d₂ e₂).comp (secondColumnAlg d₁ e₁ d₂ e₂)).toLinearMap=
      ((rename (secondColumnVars d₁ e₁ d₂ e₂)).comp (tensorValueAlg e₁ e₂)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change fourValue d₁ e₁ d₂ e₂ ((1⊗ₜ[ℚ]u)⊗ₜ[ℚ](1⊗ₜ[ℚ]v))=
      rename (secondColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ e₂ (u⊗ₜ[ℚ]v))
    simp only [fourValue_tmul,tensorValue_tmul,OneMemClass.coe_one,map_one,one_mul,
      map_mul,rename_rename]
    rfl
  exact LinearMap.congr_fun h x

omit [Fintype I] [DecidableEq I] in
lemma fourValue_crossingColumn (d₁ e₁ d₂ e₂ : I → ℕ) (x : S e₁⊗[ℚ]S d₂) :
    fourValueAlg d₁ e₁ d₂ e₂ (crossingColumnAlg d₁ e₁ d₂ e₂ x)=
      rename (crossingColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ d₂ x) := by
  have h : ((fourValueAlg d₁ e₁ d₂ e₂).comp (crossingColumnAlg d₁ e₁ d₂ e₂)).toLinearMap=
      ((rename (crossingColumnVars d₁ e₁ d₂ e₂)).comp (tensorValueAlg e₁ d₂)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change fourValue d₁ e₁ d₂ e₂ ((1⊗ₜ[ℚ]u)⊗ₜ[ℚ](v⊗ₜ[ℚ]1))=
      rename (crossingColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ d₂ (u⊗ₜ[ℚ]v))
    simp only [fourValue_tmul,tensorValue_tmul,OneMemClass.coe_one,map_one,one_mul,mul_one,
      map_mul,rename_rename]
    rfl
  exact LinearMap.congr_fun h x

lemma fourColumns_product (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁⊗[ℚ]S d₂) (g : S e₁⊗[ℚ]S e₂) :
    firstColumnAlg d₁ e₁ d₂ e₂ f * secondColumnAlg d₁ e₁ d₂ e₂ g=
      fourInterchange d₁ e₁ d₂ e₂ (f⊗ₜ[ℚ]g) := by
  apply fourValue_injective
  change fourValueAlg d₁ e₁ d₂ e₂ (_*_)=_
  rw [map_mul,fourValue_firstColumn,fourValue_secondColumn,fourValue_interchange]

lemma rawKernel_rename {σ : Type*} (a : I → I → ℕ) (d e : I → ℕ)
    (L : (Σ i,Fin (d i)) → σ) (R : (Σ i,Fin (e i)) → σ) :
    Units.map (mapRing (rename (Sum.elim L R)).toRingHom).toMonoidHom
      (SeparationInfinity.rawInverseKernelUnit a d e)=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>affineUnit (X (R ⟨j,y⟩)-X (L ⟨i,x⟩))) := by
  simp only [SeparationInfinity.rawInverseKernelUnit,SeparationInfinity.rawFactor,
    rectangular,map_prod,map_zpow,affineUnit_map,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,
    map_sub,rename_X,Sum.elim_inl,Sum.elim_inr]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.TensorPolynomials
open scoped TensorProduct
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def tensorPolynomial (f : A →ₐ[ℚ] Polynomial A) (g : B →ₐ[ℚ] Polynomial B) :
    A⊗[ℚ]B →ₐ[ℚ] Polynomial (A⊗[ℚ]B) :=
  let L := (Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A⊗[ℚ]B)).comp f
  let R := (Polynomial.mapAlgHom (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A⊗[ℚ]B)).comp g
  Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y=>mul_comm (L x) (R y))

lemma tensorPolynomial_tmul (f : A →ₐ[ℚ] Polynomial A) (g : B →ₐ[ℚ] Polynomial B)
    (x : A) (y : B) :
    tensorPolynomial f g (x⊗ₜ[ℚ]y)=
      Polynomial.map (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A⊗[ℚ]B).toRingHom (f x)*
      Polynomial.map (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A⊗[ℚ]B).toRingHom (g y) := by
  rfl

lemma eval_map {C D : Type*} [Semiring C] [Semiring D] [Algebra ℚ C] [Algebra ℚ D]
    (φ : C →ₐ[ℚ] D) (p : Polynomial C) (t : ℚ) :
    (Polynomial.map φ.toRingHom p).eval (algebraMap ℚ D t)=φ (p.eval (algebraMap ℚ C t)) := by
  rw [Polynomial.eval_map]
  calc
    _ = Polynomial.eval₂ φ.toRingHom (φ (algebraMap ℚ C t)) p :=
      congrArg (fun x=>Polynomial.eval₂ φ.toRingHom x p) (φ.commutes t).symm
    _ = _ := Polynomial.eval₂_at_apply φ.toRingHom (algebraMap ℚ C t)

lemma tensorPolynomial_eval (f : A →ₐ[ℚ] Polynomial A) (g : B →ₐ[ℚ] Polynomial B)
    (t : ℚ) (F : A →ₗ[ℚ] A) (G : B →ₗ[ℚ] B)
    (hf : ∀ x,(f x).eval (algebraMap ℚ A t)=F x)
    (hg : ∀ y,(g y).eval (algebraMap ℚ B t)=G y) (x : A⊗[ℚ]B) :
    (tensorPolynomial f g x).eval (algebraMap ℚ (A⊗[ℚ]B) t)=TensorProduct.map F G x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,Polynomial.eval_add,hx,hy]
  | tmul x y =>
    rw [tensorPolynomial_tmul,Polynomial.eval_mul,eval_map,eval_map,hf,hg]
    simp

end ElementaryPositivity.TensorPolynomials

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.CommonTranslation ElementaryPositivity.TensorPolynomials
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance taylorTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance taylorTensorAlgebra (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance taylorFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance taylorFourAlgebra (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

noncomputable local instance taylorTensorNonUnital (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (taylorTensorRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance taylorFourNonUnital (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (taylorFourRing d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring

noncomputable def commonTaylorTensor (d e : I → ℕ) :
    S d⊗[ℚ]S e →ₐ[ℚ] Polynomial (S d⊗[ℚ]S e) :=
  tensorPolynomial (taylorS d) (taylorS e)

omit [Fintype I] [DecidableEq I] in
lemma commonTaylorTensor_eval (d e : I → ℕ) (t : ℚ) (x : S d⊗[ℚ]S e) :
    (commonTaylorTensor d e x).eval (algebraMap ℚ (S d⊗[ℚ]S e) t)=
      TensorProduct.map (translationS d t) (translationS e t) x :=
  tensorPolynomial_eval _ _ t _ _ (fun x=>taylorS_eval d x t) (fun y=>taylorS_eval e y t) x

omit [Fintype I] [DecidableEq I] in
lemma map_commonTaylorTensor (d e : I → ℕ) (x : S d⊗[ℚ] S e) :
    Polynomial.map (tensorValueAlg d e).toRingHom (commonTaylorTensor d e x)=
      taylor (tensorValue d e x) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [eval_map_rat,commonTaylorTensor_eval]
  change tensorValue d e (TensorProduct.map (translationS d t) (translationS e t) x)=
    (taylor (tensorValue d e x)).eval (C t)
  rw [tensorValue_translation,taylor_eval]
  rfl

noncomputable def fourRelativeTaylor (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂) →ₐ[ℚ]
      Polynomial ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  tensorPolynomial (commonTaylorTensor d₁ e₁) Polynomial.CAlgHom

omit [Fintype I] [DecidableEq I] in
lemma fourRelativeTaylor_eval (d₁ e₁ d₂ e₂ : I → ℕ) (t : ℚ)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    (fourRelativeTaylor d₁ e₁ d₂ e₂ x).eval (algebraMap ℚ _ t)=
      TensorProduct.map (TensorProduct.map (translationS d₁ t) (translationS e₁ t))
        (LinearMap.id : (S d₂⊗[ℚ]S e₂) →ₗ[ℚ] (S d₂⊗[ℚ]S e₂)) x :=
  tensorPolynomial_eval _ _ t _ _ (commonTaylorTensor_eval d₁ e₁ t)
    (fun _=>Polynomial.eval_C) x

omit [Fintype I] [DecidableEq I] in
lemma fourRelativeTaylor_tmul (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : S d₁⊗[ℚ]S e₁) (y : S d₂⊗[ℚ]S e₂) :
    fourRelativeTaylor d₁ e₁ d₂ e₂ (x⊗ₜ[ℚ]y)=
      Polynomial.map (Algebra.TensorProduct.includeLeft : (S d₁⊗[ℚ]S e₁) →ₐ[ℚ]
        (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)).toRingHom (commonTaylorTensor d₁ e₁ x)*
      Polynomial.C ((1 : S d₁⊗[ℚ]S e₁)⊗ₜ[ℚ]y) := by
  change tensorPolynomial (commonTaylorTensor d₁ e₁) Polynomial.CAlgHom (x⊗ₜ[ℚ]y)=_
  rw [tensorPolynomial_tmul]
  congr 1
  change Polynomial.map _ (Polynomial.C y)=Polynomial.C _
  rw [Polynomial.map_C]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma fourRelativeRaw_left (d₁ e₁ d₂ e₂ : I → ℕ) (f : MvPolynomial (CellVars d₁ e₁) ℚ) :
    fourRelativeRaw d₁ e₁ d₂ e₂ (rename Sum.inl f)=
      Polynomial.map (rename (R:=ℚ) Sum.inl).toRingHom (taylor f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [fourRelativeRaw]
  | add f g hf hg => simp only [map_add,Polynomial.map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,rename_X,taylor_X,Polynomial.map_mul,hf]
    congr 1
    simp [fourRelativeRaw]

omit [Fintype I] [DecidableEq I] in
lemma fourRelativeRaw_right (d₁ e₁ d₂ e₂ : I → ℕ) (f : MvPolynomial (CellVars d₂ e₂) ℚ) :
    fourRelativeRaw d₁ e₁ d₂ e₂ (rename Sum.inr f)=Polynomial.C (rename Sum.inr f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [fourRelativeRaw]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,rename_X,hf]
    congr 1
    simp [fourRelativeRaw]

omit [Fintype I] [DecidableEq I] in
lemma map_commonTaylorTensor_left (d₁ e₁ d₂ e₂ : I → ℕ) (x : S d₁⊗[ℚ]S e₁) :
    Polynomial.map (fourValueAlg d₁ e₁ d₂ e₂).toRingHom
      (Polynomial.map (Algebra.TensorProduct.includeLeft : (S d₁⊗[ℚ]S e₁) →ₐ[ℚ]
        (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)).toRingHom (commonTaylorTensor d₁ e₁ x))=
      Polynomial.map (rename (R:=ℚ) Sum.inl).toRingHom (taylor (tensorValue d₁ e₁ x)) := by
  rw [←map_commonTaylorTensor d₁ e₁ x,Polynomial.map_map,Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro g
  change fourValue d₁ e₁ d₂ e₂ (g⊗ₜ[ℚ]1)=rename Sum.inl (tensorValue d₁ e₁ g)
  rw [fourValue_tmul]
  change _*rename Sum.inr (tensorValueAlg d₂ e₂ 1)=_
  rw [map_one,map_one,mul_one]

omit [Fintype I] [DecidableEq I] in
lemma map_fourRelativeTaylor (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    Polynomial.map (fourValueAlg d₁ e₁ d₂ e₂).toRingHom (fourRelativeTaylor d₁ e₁ d₂ e₂ x)=
      fourRelativeRaw d₁ e₁ d₂ e₂ (fourValue d₁ e₁ d₂ e₂ x) := by
  have H : ((Polynomial.mapAlgHom (fourValueAlg d₁ e₁ d₂ e₂)).comp
      (fourRelativeTaylor d₁ e₁ d₂ e₂)).toLinearMap=
      ((fourRelativeRaw d₁ e₁ d₂ e₂).comp (fourValueAlg d₁ e₁ d₂ e₂)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change Polynomial.map (fourValueAlg d₁ e₁ d₂ e₂).toRingHom
      (fourRelativeTaylor d₁ e₁ d₂ e₂ (u⊗ₜ[ℚ]v))=
      fourRelativeRaw d₁ e₁ d₂ e₂ (fourValue d₁ e₁ d₂ e₂ (u⊗ₜ[ℚ]v))
    rw [fourRelativeTaylor_tmul,Polynomial.map_mul,map_commonTaylorTensor_left,
      Polynomial.map_C,fourValue_tmul,map_mul,fourRelativeRaw_left,fourRelativeRaw_right]
    congr 1
    change Polynomial.C (fourValue d₁ e₁ d₂ e₂ (1⊗ₜ[ℚ]v))=_
    rw [fourValue_tmul]
    change Polynomial.C (rename Sum.inl (tensorValueAlg d₁ e₁ 1)*_)=_
    rw [map_one,map_one,one_mul]
  exact LinearMap.congr_fun H x

end ElementaryPositivity.RawShuffle

end

end OAI

import Mathlib
import OAI.Algebra.FiniteTensor.KoszulForms
import OAI.Algebra.FiniteTensor.TensorCoordinates

namespace OAI

/-! Tensor products of differential forms and head-tail tensor equivalences. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation
variable (K σ τ : Type*) [Field K]
variable (p : ℕ)

def inlForm : Space K σ p →ₐ[K] Space K (σ ⊕ τ) p :=
  Algebra.TensorProduct.map (rename K σ p Sum.inl) (inlExterior K σ τ)
def inrForm : Space K τ p →ₐ[K] Space K (σ ⊕ τ) p :=
  Algebra.TensorProduct.map (rename K τ p Sum.inr) (inrExterior K σ τ)

 
def productEquiv : (Space K σ p ⊗[K] Space K τ p) ≃ₗ[K] Space K (σ ⊕ τ) p :=
  (TensorProduct.tensorTensorTensorComm K (A K σ p) (E K σ) (A K τ p) (E K τ)).trans
    (TensorProduct.congr (sumTensorEquiv K σ p τ).symm.toLinearEquiv
      (sumExteriorEquiv K σ τ).symm)

@[simp] theorem productEquiv_tmul (ω : Space K σ p) (η : Space K τ p) :
    productEquiv K σ τ p (ω ⊗ₜ[K] η) = inlForm K σ τ p ω * inrForm K σ τ p η := by
  let M : Space K σ p ⊗[K] Space K τ p →ₗ[K] Space K (σ ⊕ τ) p :=
    TensorProduct.lift ((LinearMap.mul K (Space K (σ ⊕ τ) p)).compl₁₂
      (inlForm K σ τ p).toLinearMap (inrForm K σ τ p).toLinearMap)
  have hM : (productEquiv K σ τ p).toLinearMap=M := by
    apply TensorProduct.ext_fourfold'
    intro a e b f
    simp only [productEquiv,LinearEquiv.coe_coe,LinearEquiv.trans_apply,
      TensorProduct.tensorTensorTensorComm_tmul,TensorProduct.congr_tmul,
      sumExteriorEquiv_symm_tmul,M,TensorProduct.lift.tmul,LinearMap.compl₁₂_apply,
      LinearMap.mul_apply',AlgHom.toLinearMap_apply,inlForm,inrForm,
      Algebra.TensorProduct.map_tmul,Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  exact LinearMap.congr_fun hM (ω ⊗ₜ[K] η)

@[simp] theorem parity_inlForm (ω : Space K σ p) :
    parity K (A K (σ ⊕ τ) p) (σ ⊕ τ) (inlForm K σ τ p ω) =
      inlForm K σ τ p (parity K (A K σ p) σ ω) := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha,hb]
  | tmul a e => simp [inlForm,inlExterior,involute_map]
@[simp] theorem parity_inrForm (ω : Space K τ p) :
    parity K (A K (σ ⊕ τ) p) (σ ⊕ τ) (inrForm K σ τ p ω) =
      inrForm K σ τ p (parity K (A K τ p) τ ω) := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha,hb]
  | tmul a e => simp [inrForm,inrExterior,involute_map]

variable [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [CharP K p]
@[simp] theorem D_inlForm (ω : Space K σ p) :
    D K (σ ⊕ τ) p (inlForm K σ τ p ω)=inlForm K σ τ p (D K σ p ω) := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha,hb]
  | tmul a e =>
    simp only [inlForm,Algebra.TensorProduct.map_tmul,D,differential_tmul,
      Fintype.sum_sum_type,map_sum,map_mul,inlExterior_dx]
    simp only [derivative_rename K σ p Sum.inl Sum.inl_injective]
    have hz (j : τ) : derivative K (σ ⊕ τ) p (Sum.inr j) (rename K σ p Sum.inl a)=0 :=
      derivative_rename_other K σ p Sum.inl (Sum.inr j) (by rintro ⟨i,h⟩; cases h) a
    simp only [hz,TensorProduct.zero_tmul,Finset.sum_const_zero,add_zero]

@[simp] theorem D_inrForm (ω : Space K τ p) :
    D K (σ ⊕ τ) p (inrForm K σ τ p ω)=inrForm K σ τ p (D K τ p ω) := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha,hb]
  | tmul a e =>
    simp only [inrForm,Algebra.TensorProduct.map_tmul,D,differential_tmul,
      Fintype.sum_sum_type,map_sum,map_mul,inrExterior_dx]
    simp only [derivative_rename K τ p Sum.inr Sum.inr_injective]
    have hz (i : σ) : derivative K (σ ⊕ τ) p (Sum.inl i) (rename K τ p Sum.inr a)=0 :=
      derivative_rename_other K τ p Sum.inr (Sum.inl i) (by rintro ⟨j,h⟩; cases h) a
    simp only [hz,TensorProduct.zero_tmul,Finset.sum_const_zero,zero_add]

 
theorem D_product (ω : Space K σ p) (η : Space K τ p) :
    D K (σ ⊕ τ) p (productEquiv K σ τ p (ω ⊗ₜ[K] η)) =
      productEquiv K σ τ p (D K σ p ω ⊗ₜ[K] η +
        parity K (A K σ p) σ ω ⊗ₜ[K] D K τ p η) := by
  simp only [productEquiv_tmul,D_mul,D_inlForm,D_inrForm,parity_inlForm,map_add]

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation
variable (K σ τ : Type*) [Field K] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
variable (p : ℕ) [CharP K p]

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [CharP K p] in
@[simp] theorem inlForm_scalar (a : A K σ p) :
    inlForm K σ τ p (scalar K (A K σ p) σ a)=
      scalar K (A K (σ ⊕ τ) p) (σ ⊕ τ) (rename K σ p Sum.inl a) := by
  simp [inlForm,scalar]
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [CharP K p] in
@[simp] theorem inrForm_scalar (a : A K τ p) :
    inrForm K σ τ p (scalar K (A K τ p) τ a)=
      scalar K (A K (σ ⊕ τ) p) (σ ⊕ τ) (rename K τ p Sum.inr a) := by
  simp [inrForm,scalar]

theorem D_scalar_anticommute (b : A K σ p) (ω : Space K σ p) :
    D K σ p (scalar K (A K σ p) σ b) * ω =
      parity K (A K σ p) σ ω * D K σ p (scalar K (A K σ p) σ b) := by
  rw [D,differential_scalar]
  exact oneForm_anticommute _ _

 
theorem koszul_product (S : A K σ p) (T : A K τ p)
    (ω : Space K σ p) (η : Space K τ p) :
    koszul K (σ ⊕ τ) p (rename K σ p Sum.inl S + rename K τ p Sum.inr T)
        (productEquiv K σ τ p (ω ⊗ₜ[K] η)) =
      productEquiv K σ τ p (koszul K σ p S ω ⊗ₜ[K] η +
        parity K (A K σ p) σ ω ⊗ₜ[K] koszul K τ p T η) := by
  simp only [koszul,LinearMap.mulLeft_apply,productEquiv_tmul,map_add,scalar_add,add_mul]
  rw [← inlForm_scalar,← inrForm_scalar,D_inlForm]
  simp only [map_mul]
  congr 1
  · rw [mul_assoc]
  · rw [← mul_assoc,inrForm_scalar,D_scalar_anticommute,parity_inlForm,mul_assoc,
      ← inrForm_scalar,D_inrForm]

 
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [CharP K p] in
theorem mulScalar_product_left (b : A K σ p) (ω : Space K σ p) (η : Space K τ p) :
    mulScalar K (σ ⊕ τ) p (rename K σ p Sum.inl b)
        (productEquiv K σ τ p (ω ⊗ₜ[K] η)) =
      productEquiv K σ τ p (mulScalar K σ p b ω ⊗ₜ[K] η) := by
  simp only [mulScalar,LinearMap.mulLeft_apply,productEquiv_tmul,map_mul,inlForm_scalar,mul_assoc]

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [CharP K p] in
theorem mulScalar_product_right (b : A K τ p) (ω : Space K σ p) (η : Space K τ p) :
    mulScalar K (σ ⊕ τ) p (rename K τ p Sum.inr b)
        (productEquiv K σ τ p (ω ⊗ₜ[K] η)) =
      productEquiv K σ τ p (ω ⊗ₜ[K] mulScalar K τ p b η) := by
  simp only [mulScalar,LinearMap.mulLeft_apply,productEquiv_tmul,map_mul,inrForm_scalar]
  rw [← mul_assoc,scalar_commute,mul_assoc]

end
end PD4Tensor.TruncatedForms

 

namespace PD4Tensor
noncomputable section
open scoped TensorProduct
variable (K : Type*) [Field K] {n : ℕ} (V : Fin (n+1) → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

def headTailTo : (⨂[K] i, V i) →ₗ[K] V 0 ⊗[K] (⨂[K] i : Fin n, V i.succ) :=
  PiTensorProduct.lift (LinearMap.uncurryLeft
    { toFun := fun x => (TensorProduct.mk K _ _ x).compMultilinearMap (PiTensorProduct.tprod K)
      map_add' := by intro x y; ext v; simp
      map_smul' := by intro c x; ext v; simp [TensorProduct.smul_tmul'] })

def headTailFrom : V 0 ⊗[K] (⨂[K] i : Fin n, V i.succ) →ₗ[K] (⨂[K] i, V i) :=
  TensorProduct.lift (PiTensorProduct.lift.toLinearMap.comp (PiTensorProduct.tprod K).curryLeft)

@[simp] theorem headTailTo_tprod (v : ∀ i, V i) :
    headTailTo K V (PiTensorProduct.tprod K v)=
      v 0 ⊗ₜ[K] PiTensorProduct.tprod K (fun i : Fin n => v i.succ) := by
  simp only [headTailTo,PiTensorProduct.lift.tprod,LinearMap.uncurryLeft_apply,
    LinearMap.coe_mk, AddHom.coe_mk,LinearMap.compMultilinearMap_apply,TensorProduct.mk_apply]
  rfl
@[simp] theorem headTailFrom_tmul (x : V 0) (v : ∀ i : Fin n, V i.succ) :
    headTailFrom K V (x ⊗ₜ[K] PiTensorProduct.tprod K v)=
      PiTensorProduct.tprod K (Fin.cons x v) := by simp [headTailFrom]

 
def headTailEquiv : (⨂[K] i, V i) ≃ₗ[K] V 0 ⊗[K] (⨂[K] i : Fin n, V i.succ) :=
  LinearEquiv.ofLinearMap (headTailTo K V) (headTailFrom K V) (by
    apply TensorProduct.ext'
    intro x z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod c v => simp [headTailFrom,headTailTo]
    | add a b ha hb =>
      simp only [LinearMap.comp_apply,LinearMap.id_apply] at ha hb ⊢
      simp only [TensorProduct.tmul_add,map_add,ha,hb]) (by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
      headTailTo_tprod,headTailFrom_tmul,LinearMap.id_apply]
    congr 1
    ext i
    cases i using Fin.cases <;> rfl)

@[simp] theorem headTailEquiv_tprod (v : ∀ i, V i) :
    headTailEquiv K V (PiTensorProduct.tprod K v)=
      v 0 ⊗ₜ[K] PiTensorProduct.tprod K (fun i : Fin n => v i.succ) := headTailTo_tprod K V v

end
end PD4Tensor
end

end OAI

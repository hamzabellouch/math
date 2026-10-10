import Mathlib
import OAI.Algebra.FiniteTensor.OddTensors

namespace OAI

/-! Separated block forms and compatibility of differential and multiplication operators. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation
universe u

def BlockCoords : (n : ℕ) → (Fin (n+1) → Type u) → Type u
  | 0, σ => σ 0
  | n+1, σ => σ 0 ⊕ BlockCoords n (fun i => σ i.succ)

instance blockFintype (n : ℕ) (σ : Fin (n+1) → Type u) [∀ i, Fintype (σ i)] :
    Fintype (BlockCoords n σ) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (σ 0))
  | succ n ih =>
    let := ih (fun i => σ i.succ)
    exact inferInstanceAs (Fintype (σ 0 ⊕ BlockCoords n (fun i => σ i.succ)))

instance blockDecEq (n : ℕ) (σ : Fin (n+1) → Type u) [∀ i, DecidableEq (σ i)] :
    DecidableEq (BlockCoords n σ) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq (σ 0))
  | succ n ih =>
    let := ih (fun i => σ i.succ)
    exact inferInstanceAs (DecidableEq (σ 0 ⊕ BlockCoords n (fun i => σ i.succ)))

variable (K : Type*) [Field K] (p : ℕ)

def separatedEquiv : {n : ℕ} → (σ : Fin (n+1) → Type u) →
    [∀ i, Fintype (σ i)] → [∀ i, DecidableEq (σ i)] →
    (⨂[K] i, Space K (σ i) p) ≃ₗ[K] Space K (BlockCoords n σ) p
  | 0, _, _, _ => PiTensorProduct.subsingletonEquiv (0 : Fin 1)
  | n+1, σ, _, _ => (headTailEquiv K (fun i => Space K (σ i) p)).trans
    ((TensorProduct.congr (LinearEquiv.refl K _) (separatedEquiv (fun i => σ i.succ))).trans
      (productEquiv K (σ 0) (BlockCoords n (fun i => σ i.succ)) p))

@[simp] theorem separatedEquiv_zero (σ : Fin 1 → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (v : ∀ i, Space K (σ i) p) :
    separatedEquiv K p σ (PiTensorProduct.tprod K v)=v 0 :=
  PiTensorProduct.subsingletonEquiv_apply_tprod _ _

theorem separatedEquiv_succ {n : ℕ} (σ : Fin (n+1+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (v : ⨂[K] i, Space K (σ i) p) :
    separatedEquiv K p σ v = productEquiv K (σ 0) (BlockCoords n (fun i => σ i.succ)) p
      (TensorProduct.map LinearMap.id (separatedEquiv K p (fun i => σ i.succ)).toLinearMap
        (headTailEquiv K (fun i => Space K (σ i) p) v)) := rfl

@[simp] theorem separatedEquiv_succ_tprod {n : ℕ} (σ : Fin (n+1+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (v : ∀ i, Space K (σ i) p) :
    separatedEquiv K p σ (PiTensorProduct.tprod K v) =
      productEquiv K (σ 0) (BlockCoords n (fun i => σ i.succ)) p
        (v 0 ⊗ₜ[K] separatedEquiv K p (fun i => σ i.succ)
          (PiTensorProduct.tprod K (fun i => v i.succ))) := by
  rw [separatedEquiv_succ,headTailEquiv_tprod,TensorProduct.map_tmul,LinearMap.id_apply]
  rfl

variable [CharP K p]

theorem D_separated {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (v : ⨂[K] i, Space K (σ i) p) :
    D K (BlockCoords n σ) p (separatedEquiv K p σ v) =
      separatedEquiv K p σ (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
        (fun i => D K (σ i) p) v) := by
  induction n with
  | zero =>
    have heq : (D K (BlockCoords 0 σ) p).comp (separatedEquiv K p σ).toLinearMap =
        (separatedEquiv K p σ).toLinearMap.comp
          (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
            (fun i => D K (σ i) p)) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro w
      simp [oddTensor,oddCoordinate]
      rfl
    exact LinearMap.congr_fun heq v
  | succ n ih =>
    have heq : (D K (BlockCoords (n+1) σ) p).comp (separatedEquiv K p σ).toLinearMap =
        (separatedEquiv K p σ).toLinearMap.comp
          (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
            (fun i => D K (σ i) p)) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro w
      simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
        LinearEquiv.coe_coe,separatedEquiv_succ_tprod]
      change D K (σ 0 ⊕ BlockCoords n (fun i => σ i.succ)) p _ = _
      rw [D_product]
      rw [separatedEquiv_succ]
      rw [show headTailEquiv K (fun i => Space K (σ i) p)
          (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
            (fun i => D K (σ i) p) (PiTensorProduct.tprod K w)) = _ from
        LinearMap.congr_fun (headTail_oddTensor
          (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
          (fun i => D K (σ i) p)) (PiTensorProduct.tprod K w)]
      simp only [LinearMap.comp_apply,headTailEquiv_tprod,LinearMap.add_apply,
        TensorProduct.map_tmul,LinearMap.id_apply,map_add,LinearEquiv.coe_coe]
      rw [ih]
      rfl
    exact LinearMap.congr_fun heq v

omit [CharP K p] in
@[simp] theorem parity_product (σ τ : Type*) [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (ω : Space K σ p) (η : Space K τ p) :
    parity K (A K (σ ⊕ τ) p) (σ ⊕ τ) (productEquiv K σ τ p (ω ⊗ₜ[K] η)) =
      productEquiv K σ τ p
        (parity K (A K σ p) σ ω ⊗ₜ[K] parity K (A K τ p) τ η) := by
  simp only [productEquiv_tmul,map_mul,parity_inlForm,parity_inrForm]

omit [CharP K p] in
theorem parity_separated {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (v : ⨂[K] i, Space K (σ i) p) :
    parity K (A K (BlockCoords n σ) p) (BlockCoords n σ) (separatedEquiv K p σ v) =
      separatedEquiv K p σ
        (PiTensorProduct.map (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap) v) := by
  induction n with
  | zero =>
    have heq : (parity K (A K (BlockCoords 0 σ) p) (BlockCoords 0 σ)).toLinearMap.comp
        (separatedEquiv K p σ).toLinearMap =
        (separatedEquiv K p σ).toLinearMap.comp
          (PiTensorProduct.map (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro w
      simp
      rfl
    exact LinearMap.congr_fun heq v
  | succ n ih =>
    have heq : (parity K (A K (BlockCoords (n+1) σ) p) (BlockCoords (n+1) σ)).toLinearMap.comp
        (separatedEquiv K p σ).toLinearMap =
        (separatedEquiv K p σ).toLinearMap.comp
          (PiTensorProduct.map (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro w
      simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
        LinearEquiv.coe_coe,AlgHom.toLinearMap_apply,PiTensorProduct.map_tprod,
        separatedEquiv_succ_tprod]
      change parity K (A K (σ 0 ⊕ BlockCoords n (fun i => σ i.succ)) p)
        (σ 0 ⊕ BlockCoords n (fun i => σ i.succ)) _ = _
      rw [parity_product,ih,PiTensorProduct.map_tprod]
      rfl
    exact LinearMap.congr_fun heq v

def separatedPotential : {n : ℕ} → (σ : Fin (n+1) → Type u) →
    [∀ i, Fintype (σ i)] → [∀ i, DecidableEq (σ i)] →
    (∀ i, A K (σ i) p) → A K (BlockCoords n σ) p
  | 0, _, _, _, S => S 0
  | n+1, σ, _, _, S =>
    rename K (σ 0) p Sum.inl (S 0) +
      rename K (BlockCoords n (fun i => σ i.succ)) p Sum.inr
        (separatedPotential (fun i => σ i.succ) (fun i => S i.succ))

theorem koszul_separated {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)]
    (S : ∀ i, A K (σ i) p) (v : ⨂[K] i, Space K (σ i) p) :
    koszul K (BlockCoords n σ) p (separatedPotential K p σ S) (separatedEquiv K p σ v) =
      separatedEquiv K p σ (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
        (fun i => koszul K (σ i) p (S i)) v) := by
  induction n with
  | zero =>
    have heq : (koszul K (BlockCoords 0 σ) p (separatedPotential K p σ S)).comp
        (separatedEquiv K p σ).toLinearMap =
        (separatedEquiv K p σ).toLinearMap.comp
          (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
            (fun i => koszul K (σ i) p (S i))) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro w
      simp [oddTensor,oddCoordinate]
      rfl
    exact LinearMap.congr_fun heq v
  | succ n ih =>
    have heq : (koszul K (BlockCoords (n+1) σ) p (separatedPotential K p σ S)).comp
        (separatedEquiv K p σ).toLinearMap =
        (separatedEquiv K p σ).toLinearMap.comp
          (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
            (fun i => koszul K (σ i) p (S i))) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro w
      simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
        LinearEquiv.coe_coe,separatedEquiv_succ_tprod]
      change koszul K (σ 0 ⊕ BlockCoords n (fun i => σ i.succ)) p
        (rename K (σ 0) p Sum.inl (S 0) +
          rename K (BlockCoords n (fun i => σ i.succ)) p Sum.inr
            (separatedPotential K p (fun i => σ i.succ) (fun i => S i.succ))) _ = _
      rw [koszul_product,separatedEquiv_succ]
      rw [show headTailEquiv K (fun i => Space K (σ i) p)
          (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
            (fun i => koszul K (σ i) p (S i)) (PiTensorProduct.tprod K w)) = _ from
        LinearMap.congr_fun (headTail_oddTensor
          (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
          (fun i => koszul K (σ i) p (S i))) (PiTensorProduct.tprod K w)]
      simp only [LinearMap.comp_apply,headTailEquiv_tprod,LinearMap.add_apply,
        TensorProduct.map_tmul,LinearMap.id_apply,map_add,LinearEquiv.coe_coe]
      rw [ih]
      rfl
    exact LinearMap.congr_fun heq v

 
omit [CharP K p] in
theorem mulScalar_product (σ τ : Type*) [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (a : A K σ p) (b : A K τ p)
    (ω : Space K σ p) (η : Space K τ p) :
    mulScalar K (σ ⊕ τ) p (rename K σ p Sum.inl a * rename K τ p Sum.inr b)
        (productEquiv K σ τ p (ω ⊗ₜ[K] η)) =
      productEquiv K σ τ p (mulScalar K σ p a ω ⊗ₜ[K] mulScalar K τ p b η) := by
  have h (x y : A K (σ ⊕ τ) p) (v : Space K (σ ⊕ τ) p) :
      mulScalar K (σ ⊕ τ) p (x*y) v =
        mulScalar K (σ ⊕ τ) p x (mulScalar K (σ ⊕ τ) p y v) := by
    simp only [mulScalar,LinearMap.mulLeft_apply,scalar_mul,mul_assoc]
  rw [h,mulScalar_product_right,mulScalar_product_left]

def separatedProduct : {n : ℕ} → (σ : Fin (n+1) → Type u) →
    [∀ i, Fintype (σ i)] → [∀ i, DecidableEq (σ i)] →
    (∀ i, A K (σ i) p) → A K (BlockCoords n σ) p
  | 0, _, _, _, b => b 0
  | n+1, σ, _, _, b =>
    rename K (σ 0) p Sum.inl (b 0) *
      rename K (BlockCoords n (fun i => σ i.succ)) p Sum.inr
        (separatedProduct (fun i => σ i.succ) (fun i => b i.succ))

 

omit [CharP K p] in
theorem mulScalar_separated {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)]
    (b : ∀ i, A K (σ i) p) (v : ⨂[K] i, Space K (σ i) p) :
    mulScalar K (BlockCoords n σ) p (separatedProduct K p σ b) (separatedEquiv K p σ v) =
      separatedEquiv K p σ (PiTensorProduct.map (fun i => mulScalar K (σ i) p (b i)) v) := by
  induction n with
  | zero =>
    have heq : (mulScalar K (BlockCoords 0 σ) p (separatedProduct K p σ b)).comp
        (separatedEquiv K p σ).toLinearMap =
        (separatedEquiv K p σ).toLinearMap.comp
          (PiTensorProduct.map (fun i => mulScalar K (σ i) p (b i))) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro w
      simp
      rfl
    exact LinearMap.congr_fun heq v
  | succ n ih =>
    have heq : (mulScalar K (BlockCoords (n+1) σ) p (separatedProduct K p σ b)).comp
        (separatedEquiv K p σ).toLinearMap =
        (separatedEquiv K p σ).toLinearMap.comp
          (PiTensorProduct.map (fun i => mulScalar K (σ i) p (b i))) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro w
      simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
        LinearEquiv.coe_coe,PiTensorProduct.map_tprod,separatedEquiv_succ_tprod]
      change mulScalar K (σ 0 ⊕ BlockCoords n (fun i => σ i.succ)) p
        (rename K (σ 0) p Sum.inl (b 0) *
          rename K (BlockCoords n (fun i => σ i.succ)) p Sum.inr
            (separatedProduct K p (fun i => σ i.succ) (fun i => b i.succ))) _ = _
      rw [mulScalar_product,ih,PiTensorProduct.map_tprod]
    exact LinearMap.congr_fun heq v

end
end PD4Tensor.TruncatedForms
end

end OAI

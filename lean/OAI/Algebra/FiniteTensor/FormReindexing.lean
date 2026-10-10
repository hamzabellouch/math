import Mathlib
import OAI.Algebra.FiniteTensor.SeparatedForms

namespace OAI

/-! Exterior reindexing, separated potentials and parity of Koszul operators. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Forms
noncomputable section
open scoped TensorProduct
variable (K A B σ τ : Type*) [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

def coordinateIsometry (e : σ ≃ τ) :
    (0 : QuadraticForm K (σ → K)).IsometryEquiv (0 : QuadraticForm K (τ → K)) :=
  { LinearEquiv.funCongrLeft K K e.symm with
    map_app' := by intro x; rfl }

def reindexExterior (e : σ ≃ τ) : E K σ ≃ₐ[K] E K τ :=
  CliffordAlgebra.equivOfIsometry (coordinateIsometry K σ τ e)

@[simp] theorem reindexExterior_ι (e : σ ≃ τ) (v : σ → K) :
    reindexExterior K σ τ e (ExteriorAlgebra.ι K v)=
      ExteriorAlgebra.ι K (fun j => v (e.symm j)) := by
  change CliffordAlgebra.map (coordinateIsometry K σ τ e).toIsometry (CliffordAlgebra.ι _ v)=_
  rw [CliffordAlgebra.map_apply_ι]
  rfl

@[simp] theorem reindexExterior_dx [DecidableEq σ] [DecidableEq τ] (e : σ ≃ τ) (i : σ) :
    reindexExterior K σ τ e (dx K σ i)=dx K τ (e i) := by
  rw [dx,reindexExterior_ι,dx]
  congr 1
  funext j
  simp only [Pi.single_apply]
  have h : e.symm j=i ↔ j=e i := e.symm_apply_eq
  simp only [h]

theorem reindexExterior_parity (e : σ ≃ τ) (v : E K σ) :
    reindexExterior K σ τ e (CliffordAlgebra.involute v)=
      CliffordAlgebra.involute (reindexExterior K σ τ e v) := by
  induction v using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | mul a b ha hb => simp only [map_mul,ha,hb]

 
def reindexForms (e : σ ≃ τ) (f : A ≃ₐ[K] B) : Ω K A σ ≃ₐ[K] Ω K B τ :=
  Algebra.TensorProduct.congr f (reindexExterior K σ τ e)

@[simp] theorem reindexForms_tmul (e : σ ≃ τ) (f : A ≃ₐ[K] B) (a : A) (v : E K σ) :
    reindexForms K A B σ τ e f (a ⊗ₜ[K] v)=f a ⊗ₜ[K] reindexExterior K σ τ e v := rfl

@[simp] theorem reindexForms_scalar (e : σ ≃ τ) (f : A ≃ₐ[K] B) (a : A) :
    reindexForms K A B σ τ e f (scalar K A σ a)=scalar K B τ (f a) := by
  simp only [scalar,reindexForms_tmul,map_one]

theorem reindexForms_differential [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (e : σ ≃ τ) (f : A ≃ₐ[K] B)
    (derA : σ → A →ₗ[K] A) (derB : τ → B →ₗ[K] B)
    (hder : ∀ i a, derB (e i) (f a)=f (derA i a)) (ω : Ω K A σ) :
    reindexForms K A B σ τ e f (differential K A σ derA ω)=
      differential K B τ derB (reindexForms K A B σ τ e f ω) := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a v =>
    simp only [differential_tmul,map_sum,reindexForms_tmul,map_mul,reindexExterior_dx]
    exact Fintype.sum_equiv e _ _ (fun i => by rw [hder])

theorem reindexForms_parity (e : σ ≃ τ) (f : A ≃ₐ[K] B) (ω : Ω K A σ) :
    reindexForms K A B σ τ e f (parity K A σ ω)=
      parity K B τ (reindexForms K A B σ τ e f ω) := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a v => simp only [parity_tmul,reindexForms_tmul,reindexExterior_parity]

end
end PD4Tensor.Forms

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
variable (K σ τ : Type*) [Field K] (p : ℕ)

def coordinateEquiv (e : σ ≃ τ) : Ring K σ p ≃ₐ[K] Ring K τ p :=
  AlgEquiv.ofAlgHom (rename K σ p e) (rename K τ p e.symm)
    (by apply hom_ext; intro i; simp)
    (by apply hom_ext; intro i; simp)

@[simp] theorem coordinateEquiv_coord (e : σ ≃ τ) (i : σ) :
    coordinateEquiv K σ τ p e (coord K σ p i)=coord K τ p (e i) :=
  rename_coord K σ p e i

variable [CharP K p]
theorem coordinateEquiv_derivative (e : σ ≃ τ) (i : σ) (a : Ring K σ p) :
    derivative K τ p (e i) (coordinateEquiv K σ τ p e a)=
      coordinateEquiv K σ τ p e (derivative K σ p i a) :=
  derivative_rename K σ p e e.injective i a

end
end PD4Tensor.FrobeniusTruncation

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation
universe u

def sigmaHeadTail {n : ℕ} (σ : Fin (n+1) → Type u) :
    ((i : Fin (n+1)) × σ i) ≃ σ 0 ⊕ ((i : Fin n) × σ i.succ) where
  toFun v := Fin.cases (fun x => Sum.inl x) (fun i x => Sum.inr ⟨i,x⟩) v.1 v.2
  invFun := Sum.elim (fun x => ⟨0,x⟩) (fun v => ⟨v.1.succ,v.2⟩)
  left_inv := by rintro ⟨i,x⟩; cases i using Fin.cases <;> rfl
  right_inv := by rintro (x|⟨i,x⟩) <;> rfl

 

def blockSigmaEquiv : {n : ℕ} → (σ : Fin (n+1) → Type u) →
    BlockCoords n σ ≃ ((i : Fin (n+1)) × σ i)
  | 0, σ => {
    toFun := fun x => ⟨0,x⟩
    invFun := fun v => cast (congrArg σ (Fin.eq_zero v.1)) v.2
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨i,x⟩
      have hi := Fin.eq_zero i
      subst i
      rfl }
  | n+1, σ => (Equiv.sumCongr (Equiv.refl (σ 0))
      (blockSigmaEquiv (fun i => σ i.succ))).trans (sigmaHeadTail σ).symm

@[simp] theorem blockSigmaEquiv_zero (σ : Fin 1 → Type u) (x : σ 0) :
    blockSigmaEquiv σ x=⟨0,x⟩ := rfl
@[simp] theorem blockSigmaEquiv_inl {n : ℕ} (σ : Fin (n+1+1) → Type u) (x : σ 0) :
    blockSigmaEquiv σ (Sum.inl x)=⟨0,x⟩ := rfl
@[simp] theorem blockSigmaEquiv_inr {n : ℕ} (σ : Fin (n+1+1) → Type u)
    (x : BlockCoords n (fun i => σ i.succ)) :
    blockSigmaEquiv σ (Sum.inr x)=
      ⟨(blockSigmaEquiv (fun i => σ i.succ) x).1.succ,
        (blockSigmaEquiv (fun i => σ i.succ) x).2⟩ := rfl

variable (K : Type*) [Field K] (p : ℕ)

 

def sigmaSeparatedEquiv {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] :
    (⨂[K] i, Space K (σ i) p) ≃ₗ[K] Space K ((i : Fin (n+1)) × σ i) p :=
  (separatedEquiv K p σ).trans
    (reindexForms K _ _ _ _ (blockSigmaEquiv σ)
      (coordinateEquiv K _ _ p (blockSigmaEquiv σ))).toLinearEquiv

variable [CharP K p]

theorem D_sigmaSeparated {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (v : ⨂[K] i, Space K (σ i) p) :
    D K ((i : Fin (n+1)) × σ i) p (sigmaSeparatedEquiv K p σ v) =
      sigmaSeparatedEquiv K p σ (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
        (fun i => D K (σ i) p) v) := by
  change differential K _ _ _ (reindexForms K _ _ _ _ _ _ (separatedEquiv K p σ v))=_
  rw [←reindexForms_differential K _ _ _ _ _ _ _ _
    (coordinateEquiv_derivative K _ _ p (blockSigmaEquiv σ))]
  change reindexForms K _ _ _ _ _ _ (D K _ p (separatedEquiv K p σ v))=_
  rw [D_separated]
  rfl

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
variable (K σ τ υ : Type*) [Field K] (p : ℕ)

theorem rename_rename (f : σ → τ) (g : τ → υ) (a : Ring K σ p) :
    rename K τ p g (rename K σ p f a)=rename K σ p (g ∘ f) a := by
  have h : (rename K τ p g).comp (rename K σ p f)=rename K σ p (g ∘ f) := by
    apply hom_ext
    intro i
    simp only [AlgHom.comp_apply,rename_coord,Function.comp_apply]
  exact AlgHom.congr_fun h a

@[simp] theorem coordinateEquiv_eq_rename (e : σ ≃ τ) (a : Ring K σ p) :
    coordinateEquiv K σ τ p e a=rename K σ p e a := rfl

end
end PD4Tensor.FrobeniusTruncation

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation
universe u
variable (K : Type*) [Field K] (p : ℕ)

 
def sigmaPotential {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (S : ∀ i, A K (σ i) p) :
    A K ((i : Fin (n+1)) × σ i) p :=
  ∑ i, rename K (σ i) p (Sigma.mk i) (S i)

 
def sigmaProduct {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (b : ∀ i, A K (σ i) p) :
    A K ((i : Fin (n+1)) × σ i) p :=
  ∏ i, rename K (σ i) p (Sigma.mk i) (b i)

theorem separatedPotential_reindex {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (S : ∀ i, A K (σ i) p) :
    coordinateEquiv K _ _ p (blockSigmaEquiv σ) (separatedPotential K p σ S)=
      sigmaPotential K p σ S := by
  induction n with
  | zero =>
    change rename K (σ 0) p (Sigma.mk 0) (S 0)=
      ∑ i : Fin 1, rename K (σ i) p (Sigma.mk i) (S i)
    rw [Fin.sum_univ_one]
  | succ n ih =>
    change rename K (σ 0 ⊕ BlockCoords n (fun i => σ i.succ)) p (blockSigmaEquiv σ)
      (rename K (σ 0) p Sum.inl (S 0) +
        rename K (BlockCoords n (fun i => σ i.succ)) p Sum.inr
          (separatedPotential K p (fun i => σ i.succ) (fun i => S i.succ)))=
      ∑ i, rename K (σ i) p (Sigma.mk i) (S i)
    rw [map_add]
    erw [rename_rename,rename_rename]
    rw [Fin.sum_univ_succ]
    congr 1
    have h := congrArg
      (rename K ((i : Fin (n+1)) × σ i.succ) p
        (fun v => (⟨v.1.succ,v.2⟩ : (i : Fin (n+1+1)) × σ i)))
      (ih (fun i => σ i.succ) (fun i => S i.succ))
    simp only [coordinateEquiv_eq_rename,sigmaPotential,map_sum,rename_rename,Function.comp_def] at h
    exact h

theorem separatedProduct_reindex {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (b : ∀ i, A K (σ i) p) :
    coordinateEquiv K _ _ p (blockSigmaEquiv σ) (separatedProduct K p σ b)=
      sigmaProduct K p σ b := by
  induction n with
  | zero =>
    change rename K (σ 0) p (Sigma.mk 0) (b 0)=
      ∏ i : Fin 1, rename K (σ i) p (Sigma.mk i) (b i)
    rw [Fin.prod_univ_one]
  | succ n ih =>
    change rename K (σ 0 ⊕ BlockCoords n (fun i => σ i.succ)) p (blockSigmaEquiv σ)
      (rename K (σ 0) p Sum.inl (b 0) *
        rename K (BlockCoords n (fun i => σ i.succ)) p Sum.inr
          (separatedProduct K p (fun i => σ i.succ) (fun i => b i.succ)))=
      ∏ i, rename K (σ i) p (Sigma.mk i) (b i)
    rw [map_mul]
    erw [rename_rename,rename_rename]
    rw [Fin.prod_univ_succ]
    congr 1
    have h := congrArg
      (rename K ((i : Fin (n+1)) × σ i.succ) p
        (fun v => (⟨v.1.succ,v.2⟩ : (i : Fin (n+1+1)) × σ i)))
      (ih (fun i => σ i.succ) (fun i => b i.succ))
    simp only [coordinateEquiv_eq_rename,sigmaProduct,map_prod,rename_rename,Function.comp_def] at h
    exact h

variable [CharP K p]

theorem reindex_koszul (σ τ : Type*) [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (e : σ ≃ τ) (S : A K σ p) (ω : Space K σ p) :
    reindexForms K (A K σ p) (A K τ p) σ τ e (coordinateEquiv K σ τ p e)
      (koszul K σ p S ω)=
      koszul K τ p (coordinateEquiv K σ τ p e S)
        (reindexForms K (A K σ p) (A K τ p) σ τ e (coordinateEquiv K σ τ p e) ω) := by
  simp only [koszul,LinearMap.mulLeft_apply,map_mul,D,
    reindexForms_differential K (A K σ p) (A K τ p) σ τ e (coordinateEquiv K σ τ p e)
      (derivative K σ p) (derivative K τ p) (coordinateEquiv_derivative K σ τ p e),
    reindexForms_scalar]

omit [CharP K p] in
theorem reindex_mulScalar (σ τ : Type*) [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] (e : σ ≃ τ) (b : A K σ p) (ω : Space K σ p) :
    reindexForms K (A K σ p) (A K τ p) σ τ e (coordinateEquiv K σ τ p e)
      (mulScalar K σ p b ω)=
      mulScalar K τ p (coordinateEquiv K σ τ p e b)
        (reindexForms K (A K σ p) (A K τ p) σ τ e (coordinateEquiv K σ τ p e) ω) := by
  simp only [mulScalar,LinearMap.mulLeft_apply,map_mul,reindexForms_scalar]

theorem koszul_sigmaSeparated {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)]
    (S : ∀ i, A K (σ i) p) (v : ⨂[K] i, Space K (σ i) p) :
    koszul K ((i : Fin (n+1)) × σ i) p (sigmaPotential K p σ S)
      (sigmaSeparatedEquiv K p σ v)=
      sigmaSeparatedEquiv K p σ
        (oddTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
          (fun i => koszul K (σ i) p (S i)) v) := by
  rw [←separatedPotential_reindex K p σ S]
  change koszul K _ p _
    (reindexForms K (A K (BlockCoords n σ) p) (A K ((i : Fin (n+1)) × σ i) p)
      _ _ (blockSigmaEquiv σ) (coordinateEquiv K _ _ p (blockSigmaEquiv σ))
      (separatedEquiv K p σ v))=_
  rw [←reindex_koszul,koszul_separated]
  rfl

omit [CharP K p] in
theorem mulScalar_sigmaSeparated {n : ℕ} (σ : Fin (n+1) → Type u)
    [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)]
    (b : ∀ i, A K (σ i) p) (v : ⨂[K] i, Space K (σ i) p) :
    mulScalar K ((i : Fin (n+1)) × σ i) p (sigmaProduct K p σ b)
      (sigmaSeparatedEquiv K p σ v)=
      sigmaSeparatedEquiv K p σ
        (PiTensorProduct.map (fun i => mulScalar K (σ i) p (b i)) v) := by
  rw [←separatedProduct_reindex K p σ b]
  change mulScalar K _ p _
    (reindexForms K (A K (BlockCoords n σ) p) (A K ((i : Fin (n+1)) × σ i) p)
      _ _ (blockSigmaEquiv σ) (coordinateEquiv K _ _ p (blockSigmaEquiv σ))
      (separatedEquiv K p σ v))=_
  rw [←reindex_mulScalar,mulScalar_separated]
  rfl

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.TruncatedForms
noncomputable section
open Forms FrobeniusTruncation
variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ)
  [CharP K p]

theorem koszul_parity (S : A K σ p) (ω : Space K σ p) :
    koszul K σ p S (parity K (A K σ p) σ ω)=
      -parity K (A K σ p) σ (koszul K σ p S ω) := by
  change D K σ p (scalar K (A K σ p) σ S) * parity K (A K σ p) σ ω =
    -parity K (A K σ p) σ (D K σ p (scalar K (A K σ p) σ S) * ω)
  rw [map_mul,D,differential_scalar,parity_oneForm,neg_mul,neg_neg]

omit [Fintype σ] [DecidableEq σ] [CharP K p] in
theorem mulScalar_parity (b : A K σ p) (ω : Space K σ p) :
    mulScalar K σ p b (parity K (A K σ p) σ ω)=
      parity K (A K σ p) σ (mulScalar K σ p b ω) := by
  change scalar K (A K σ p) σ b * parity K (A K σ p) σ ω=
    parity K (A K σ p) σ (scalar K (A K σ p) σ b * ω)
  rw [map_mul,parity_scalar]

@[simp] theorem koszul_zero : koszul K σ p 0=0 := by
  apply LinearMap.ext
  intro ω
  change D K σ p (scalar K (A K σ p) σ 0) * ω=0
  rw [scalar_zero,map_zero,zero_mul]

omit [Fintype σ] [DecidableEq σ] [CharP K p] in
@[simp] theorem mulScalar_one : mulScalar K σ p 1=LinearMap.id := by
  apply LinearMap.ext
  intro ω
  change scalar K (A K σ p) σ 1 * ω=ω
  rw [scalar_one,one_mul]

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor
noncomputable section
open scoped TensorProduct BigOperators
variable {K ι : Type*} [Field K] [Fintype ι] [LinearOrder ι]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

omit [Fintype ι] in
theorem oddCoordinate_congr_at (g f h : ∀ i,V i →ₗ[K] V i) (i : ι)
    (hh : f i=h i) : oddCoordinate g f i=oddCoordinate g h i := by
  funext j
  by_cases hji : j=i
  · subst j; simp only [oddCoordinate,lt_self_iff_false,ite_false,ite_true,hh]
  · simp only [oddCoordinate,hji,ite_false]

 
theorem oddTensor_single (g f : ∀ i,V i →ₗ[K] V i) (i : ι) :
    oddTensor g (Pi.single i (f i))=PiTensorProduct.map (oddCoordinate g f i) := by
  classical
  unfold oddTensor
  rw [Finset.sum_eq_single i]
  · rw [oddCoordinate_congr_at g (Pi.single i (f i)) f i (by simp)]
  · intro j _ hji
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply,PiTensorProduct.map_tprod,LinearMap.zero_apply]
    apply (PiTensorProduct.tprod K).map_coord_zero j
    simp [oddCoordinate,hji]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

end
end PD4Tensor
end

end OAI

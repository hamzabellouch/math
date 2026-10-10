import OAI.MathematicalPhysics.Heisenberg.RoundEnergy

namespace OAI

noncomputable section

open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.MeshPair
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicatorVector (J : Finset V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun j=>if j∈J then (1:ℝ) else 0)

lemma indicatorVector_sq (J : Finset V) : ‖indicatorVector J‖^2=(J.card:ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [indicatorVector]

lemma indicatorVector_orth (J : Finset V) (f : EuclideanSpace ℝ V)
    (hf : ∀ j∈J,f.ofLp j=1) : ⟪indicatorVector J,f-indicatorVector J⟫=0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j∈J
  · simp [indicatorVector,hj,hf j hj]
  · simp [indicatorVector,hj]

lemma euclideanMap_single (A : Matrix V V ℝ) (j k : V) :
    (euclideanMap A (WithLp.toLp 2 (Pi.single k (1:ℝ)))).ofLp j=A j k := by
  simp [euclideanMap_apply]

lemma indicatorVector_pairing (A : Matrix V V ℝ) (J : Finset V)
    (f : EuclideanSpace ℝ V) :
    ⟪euclideanMap A (indicatorVector J),f⟫=∑ j : J,∑ i,A i j.val*f.ofLp i := by
  rw [indicatorVector,pairing_columns]
  exact (Finset.sum_attach J (fun j=>∑ i,A i j*f.ofLp i)).symm

end Heisenberg.MeshPair
namespace Heisenberg.Exposure
open Heisenberg.MeshPair
variable {T V : Type} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] in
lemma exposedPrefix_column_support
    (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) (n : ℕ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (k : V)
    (hk : k∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I) :
    ∀ j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r n)∩I →
      prefixMatrix (fun i=>exposedStep s a b base P I p (r i)) n j k=0 := by
  have hs : ∀ j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I →
      (WithLp.toLp 2 (Pi.single k (1:ℝ)) : EuclideanSpace ℝ V).ofLp j=0 := by
    intro j hj
    have hjk : j≠k := fun he=>hj (he.symm ▸ hk)
    simp [hjk]
  have h := exposedSweep_supported s a b base P I p r n hr
    (WithLp.toLp 2 (Pi.single k (1:ℝ))) hs
  simpa only [exposedSweep_prefix,euclideanMap_single] using h

end Heisenberg.Exposure

open Filter Topology
open scoped RealInnerProductSpace Classical

open scoped Classical
open Filter
namespace Heisenberg.Serial

section
open Matrix Heisenberg.MeshPair
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]

def product : (n : ℕ) → (Fin n → Matrix V V ℝ) → Matrix V V ℝ
  | 0,_ => 1
  | n+1,K => product n (fun i => K i.succ)*K 0

private def split (n : ℕ) : (Fin (n+1) → B) ≃ B × (Fin n → B) where
  toFun c := (c 0,fun i => c i.succ)
  invFun c := Fin.cons c.1 c.2
  left_inv c := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv c := by rfl

theorem mean_product (n : ℕ) (w : Fin n → B → ℝ)
    (K : Fin n → B → Matrix V V ℝ) :
    (∑ c : Fin n → B,(∏ i,w i (c i)) • product n (fun i => K i (c i))) =
      product n (fun i => ∑ b,w i b • K i b) := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [Fintype.sum_equiv (split n) _
      (fun c => (w 0 c.1*(∏ i,w i.succ (c.2 i))) •
        (product n (fun i => K i.succ (c.2 i))*K 0 c.1))]
    · simp only [Fintype.sum_prod_type,product]
      have he (b : B) (c : Fin n → B) :
          (w 0 b*(∏ i,w i.succ (c i))) •
            (product n (fun i => K i.succ (c i))*K 0 b) =
          ((∏ i,w i.succ (c i)) • product n (fun i => K i.succ (c i)))*(w 0 b • K 0 b) := by
        rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_comm]
      simp_rw [he,←Finset.sum_mul,ih,←Finset.mul_sum]
    · intro c
      rw [Fin.prod_univ_succ,product]
      rfl

def follow : (n : ℕ) → (Fin n → Equiv.Perm V) → V → V
  | 0,_,v => v
  | n+1,σ,v => follow n (fun i => σ i.succ) (σ 0 v)

def survives : (n : ℕ) → (Fin (n+1) → Set V) → (Fin n → Equiv.Perm V) → V → Prop
  | 0,D,_,v => v∈D 0
  | n+1,D,σ,v => v∈D 0 ∧ survives n (fun i => D i.succ) (fun i => σ i.succ) (σ 0 v)

def projection (D : Set V) : Matrix V V ℝ := killedBetween D D 1

def walkKernel (n : ℕ) (D : Fin (n+1) → Set V) (σ : Fin n → Equiv.Perm V) : Matrix V V ℝ :=
  product n (fun i => killedBetween (D i.castSucc) (D i.succ) (σ i))*projection (D 0)

lemma projection_mul (D E F : Set V) (σ : Equiv.Perm V) :
    killedBetween D E σ*projection F=killedBetween (D∩F) E σ := by
  ext i j
  simp only [Matrix.mul_apply,projection,killedBetween,Equiv.Perm.one_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hj : j∈F <;> simp [hj,Set.mem_inter_iff]
  · intro k _ hkj
    simp [hkj]
  · simp

lemma walkKernel_succ (n : ℕ) (D : Fin (n+2) → Set V)
    (σ : Fin (n+1) → Equiv.Perm V) :
    walkKernel (n+1) D σ =
      walkKernel n (fun i => D i.succ) (fun i => σ i.succ)*killedBetween (D 0) (D 1) (σ 0) := by
  simp only [walkKernel,product,Matrix.mul_assoc,projection_mul,Set.inter_self,Fin.castSucc_zero,Fin.succ_zero_eq_one]
  congr 1
  have he : projection (D 1)*killedBetween (D 0) (D 1) (σ 0)=killedBetween (D 0) (D 1) (σ 0) := by
    ext i j
    simp only [Matrix.mul_apply,projection,killedBetween,Equiv.Perm.one_apply]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> simp_all
    · intro k _ hki
      simp [Ne.symm hki]
    · simp
  exact he.symm

theorem walkKernel_apply (n : ℕ) (D : Fin (n+1) → Set V)
    (σ : Fin n → Equiv.Perm V) (i j : V) :
    walkKernel n D σ i j = if survives n D σ j then
      if i=follow n σ j then 1 else 0 else 0 := by
  induction n generalizing i j with
  | zero =>
    simp only [walkKernel,product,one_mul,projection,killedBetween,follow,survives,Equiv.Perm.one_apply]
    by_cases hj : j∈D 0
    · by_cases hij : i=j
      · subst i; simp [hj]
      · simp [hj,hij]
    · simp [hj]
  | succ n ih =>
    rw [walkKernel_succ,Matrix.mul_apply,Finset.sum_eq_single (σ 0 j)]
    · rw [ih]
      simp only [killedBetween,follow,survives]
      have hs : survives n (fun i => D i.succ) (fun i => σ i.succ) (σ 0 j) → σ 0 j∈D 1 := by
        cases n <;> simp +contextual [survives]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [killedBetween,hk]
    · simp

end

open Matrix Heisenberg.Hitting
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma backward_profile (n : ℕ) (K : Fin n → Matrix V V ℝ) (f : Fin (n+1) → V → ℝ)
    (hf : ∀ i,(K i).transpose*ᵥ f i.succ=f i.castSucc) :
    (product n K).transpose*ᵥ f (Fin.last n)=f 0 := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [product,Matrix.transpose_mul,←Matrix.mulVec_mulVec]
    have hh := ih (fun i => K i.succ) (fun i => f i.succ) (fun i => hf i.succ)
    change (product n (fun i => K i.succ)).transpose*ᵥ f (Fin.last (n+1))=f 1 at hh
    rw [hh]
    exact hf 0

def cyclicKernel (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ) :
    Matrix (Fin (n+1) × V) (Fin (n+1) × V) ℝ :=
  fun i j => if i.1=finRotate (n+1) j.1 then K j.1 i.2 j.2 else 0

omit [DecidableEq V] in
lemma cyclicKernel_backward (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (f : Fin (n+1) × V → ℝ) (t : Fin (n+1)) (v : V) :
    backward (cyclicKernel n K) f (t,v) =
      ((K t).transpose*ᵥ (fun w => f (finRotate (n+1) t,w))) v := by
  simp only [backward,cyclicKernel,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (finRotate (n+1) t)]
  · simp [Matrix.mulVec,dotProduct]
  · intro u _ hu
    simp only [hu, ite_false, zero_mul, Finset.sum_const_zero]
  · simp

omit [DecidableEq V] in
lemma cyclicKernel_substochastic (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (hK : ∀ t,DoublySubstochastic (K t)) : DoublySubstochastic (cyclicKernel n K) := by
  constructor
  · intro ⟨t,i⟩ ⟨u,j⟩
    dsimp [cyclicKernel]
    split_ifs
    · exact (hK u).nonneg i j
    · rfl
  · intro ⟨t,i⟩
    simp only [cyclicKernel,Fintype.sum_prod_type]
    rw [Finset.sum_eq_single ((finRotate (n+1)).symm t)]
    · simpa using (hK ((finRotate (n+1)).symm t)).row i
    · intro u _ hu
      have he : t≠finRotate (n+1) u := by
        intro h
        exact hu (by rw [h,Equiv.symm_apply_apply])
      simp only [he, ite_false, Finset.sum_const_zero]
    · simp
  · intro ⟨t,j⟩
    simp only [cyclicKernel,Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (finRotate (n+1) t)]
    · simpa using (hK t).col j
    · intro u _ hu
      simp only [hu, ite_false, Finset.sum_const_zero]
    · simp

lemma cyclic_backward_return (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (f : Fin (n+1) → V → ℝ)
    (hf : ∀ t,t≠0 → (K t).transpose*ᵥ f (finRotate (n+1) t)=f t) :
    (product (n+1) K).transpose*ᵥ f 0=(K 0).transpose*ᵥ f (finRotate (n+1) 0) := by
  have hh := backward_profile n (fun i => K i.succ)
    (fun i => f (finRotate (n+1) i)) (by
      intro i
      rw [show finRotate (n+1) i.castSucc=i.succ from finRotate_of_lt i.isLt]
      exact hf i.succ (Fin.succ_ne_zero i))
  rw [finRotate_last] at hh
  rw [product,Matrix.transpose_mul,←Matrix.mulVec_mulVec,hh]

def cutTargets (n : ℕ) (T : Finset V) : Finset (Fin (n+1) × V) :=
  T.image (fun v => (0,v))

omit [Fintype V] in
lemma mem_cutTargets (n : ℕ) (T : Finset V) (t : Fin (n+1)) (v : V) :
    (t,v)∈cutTargets n T ↔ t=0 ∧ v∈T := by simp [cutTargets,and_comm,eq_comm]

theorem cyclic_hitting_energy (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ)
    (hK : ∀ t,DoublySubstochastic (K t)) (T : Finset V) :
    let F := hitting (cyclicKernel n K) (cutTargets n T)
    energy (cyclicKernel n K) F = energy (product (n+1) K) (fun v => F (0,v)) := by
  dsimp only
  let U := cyclicKernel n K
  let F := hitting U (cutTargets n T)
  have hU := cyclicKernel_substochastic n K hK
  have hf (t : Fin (n+1)) (ht : t≠0) :
      (K t).transpose*ᵥ (fun v => F (finRotate (n+1) t,v))=(fun v => F (t,v)) := by
    funext v
    rw [←cyclicKernel_backward]
    exact hitting_harmonic hU (cutTargets n T) (by simp [mem_cutTargets,ht])
  have hr := cyclic_backward_return n K (fun t v => F (t,v)) hf
  have hr' (v : V) : backward (product (n+1) K) (fun v => F (0,v)) v=backward U F (0,v) := by
    rw [cyclicKernel_backward]
    exact congrFun hr v
  rw [energy_transpose]
  change (∑ z,F z*(F z-backward U F z))=energy _ _
  rw [Fintype.sum_prod_type,Finset.sum_eq_single (0:Fin (n+1))]
  · rw [energy_transpose]
    apply Finset.sum_congr rfl
    intro v _
    rw [hr']
  · intro t _ ht
    apply Finset.sum_eq_zero
    intro v _
    have hh := hitting_harmonic hU (cutTargets n T) (i:=(t,v)) (by simp [mem_cutTargets,ht])
    change backward U F (t,v)=F (t,v) at hh
    rw [hh,sub_self,mul_zero]
  · simp

end Heisenberg.Serial

end

end OAI

import Mathlib
import OAI.Algebra.FiniteTensor.NormalResidues

namespace OAI

/-! Chart-normal cycles, coordinate reindexing and oriented residue pairings. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open PD4Tensor.Forms
variable (K R υ : Type*) [Field K] [CommRing R] [Algebra K R]
  [Fintype υ] [DecidableEq υ] (p : ℕ) [CharP R p] [Invertible (2 : K)]

def chartDerivative (i : υ) : Ring R υ (fun _ => p) →ₗ[K] Ring R υ (fun _ => p) :=
  (relativeDeriv R υ p i).restrictScalars K

variable {σ : Type*} {c : ℕ}

def normalCoordinates (e : υ ≃ σ ⊕ Fin c)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p)) : List (Ring R υ (fun _ => p)) :=
  List.ofFn (fun j => q.symm (coord R υ (fun _ => p) (e.symm (Sum.inr j))))

def chartNormal (e : υ ≃ σ ⊕ Fin c)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p)) :
    Ω K (Ring R υ (fun _ => p)) υ :=
  normalCycle K (Ring R υ (fun _ => p)) υ (chartDerivative K R υ p) p
    (normalCoordinates R υ p e q)

theorem chartNormal_closed (e : υ ≃ σ ⊕ Fin c)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p)) :
    differential K (Ring R υ (fun _ => p)) υ (chartDerivative K R υ p)
      (chartNormal K R υ p e q)=0 :=
  normalCycle_closed (chartDerivative K R υ p) (partial_mul R υ p)
    (partial_commute R υ p) p _

omit [Fintype υ] [DecidableEq υ] [CharP R p] in
private theorem normalCoordinates_span (e : υ ≃ σ ⊕ Fin c)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p)) :
    {a | a ∈ normalCoordinates R υ p e q}=
      Set.range (fun j => q.symm (coord R υ (fun _ => p) (e.symm (Sum.inr j)))) := by
  ext a
  simp only [normalCoordinates,List.mem_ofFn,Set.mem_ofPred_eq,Set.mem_range]

omit [Fintype υ] [DecidableEq υ] [CharP R p] in
private theorem normalCoordinates_pow (e : υ ≃ σ ⊕ Fin c)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p)) :
    ∀ a ∈ normalCoordinates R υ p e q, a^p=0 := by
  intro a ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  rw [←map_pow,coord_pow,map_zero]

 

theorem chartNormal_ann (hp : 0<p) (e : υ ≃ σ ⊕ Fin c)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p))
    (a : Ring R υ (fun _ => p)) (ha : splitRestriction hp e q a=0) :
    scalar K (Ring R υ (fun _ => p)) υ a * chartNormal K R υ p e q=0 ∧
      differential K (Ring R υ (fun _ => p)) υ (chartDerivative K R υ p)
        (scalar K (Ring R υ (fun _ => p)) υ a) * chartNormal K R υ p e q=0 := by
  apply normalCycle_ideal_ann (chartDerivative K R υ p) (partial_mul R υ p)
    p hp (normalCoordinates R υ p e q) (normalCoordinates_pow R υ p e q) a
  rw [normalCoordinates_span,←splitRestriction_ker hp e q]
  exact ha

 

theorem chartNormal_koszul (hp : 0<p) (e : υ ≃ σ ⊕ Fin c)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p))
    (S : Ring R υ (fun _ => p)) (hS : splitRestriction hp e q S=0) :
    oneForm K (Ring R υ (fun _ => p)) υ (fun i => chartDerivative K R υ p i S) *
      chartNormal K R υ p e q=0 := by
  have h := (chartNormal_ann K R υ p hp e q S hS).2
  simpa only [differential_scalar] using h

 

theorem chartNormal_boundary (hp : 0<p) (e : υ ≃ σ ⊕ Fin c)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p))
    (S : Ring R υ (fun _ => p)) (hS : splitRestriction hp e q S=0)
    (a : Ring R υ (fun _ => p))
    (ha : splitRestriction hp e q a ∈ Ideal.span (Set.range (fun i =>
      splitRestriction hp e q (chartDerivative K R υ p i S)))) :
    scalar K (Ring R υ (fun _ => p)) υ a * chartNormal K R υ p e q ∈
      LinearMap.range (LinearMap.mulLeft K
        (oneForm K (Ring R υ (fun _ => p)) υ (fun i => chartDerivative K R υ p i S))) := by
  apply restricted_gradient_boundary ((splitRestriction hp e q).restrictScalars K)
    (splitRestriction_surjective hp e q) (fun i => chartDerivative K R υ p i S)
    (chartNormal K R υ p e q) (chartNormal_koszul K R υ p hp e q S hS)
  · intro b hb
    exact (chartNormal_ann K R υ p hp e q b hb).1
  · exact ha

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open PD4Tensor.Forms
variable (K : Type*) [Field K] (c d p : ℕ) [CharP K p] [Fact p.Prime]
  [Invertible (2 : K)]

 

theorem chartNormal_pair_nonzero
    (e : Fin (c+d) ≃ Fin d ⊕ Fin c)
    (q : Ring K (Fin (c+d)) (fun _ => p) ≃ₐ[K] Ring K (Fin (c+d)) (fun _ => p)) :
    FrobeniusTruncation.residue K (Fin (c+d)) p (Fact.out : p.Prime).pos
      (topCoefficient K (Ring K (Fin (c+d)) (fun _ => p)) (c+d)
        (chartNormal K K (Fin (c+d)) p e q *
          chartNormal K K (Fin (c+d)) p (e.trans (Equiv.sumComm _ _)) q))≠0 := by
  let perm : Fin (c+d) ≃ Fin (c+d) :=
    finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans e.symm)
  let E := reindexEquiv K (Fin (c+d)) (Fin (c+d)) p perm
  have hn := FrobeniusTruncation.inverse_normal_residue_ne_zero K (c+d) p (E.trans q.symm)
  have hlist :
      List.ofFn (fun i => (E.trans q.symm) (coord K (Fin (c+d)) (fun _ => p) i))=
      normalCoordinates K (Fin (c+d)) p e q ++
        normalCoordinates K (Fin (c+d)) p (e.trans (Equiv.sumComm _ _)) q := by
    rw [List.ofFn_add]
    apply congrArg₂ List.append
    · apply congrArg List.ofFn
      funext i
      simp only [AlgEquiv.trans_apply,E,reindexEquiv_coord,perm,Equiv.trans_apply,
        Equiv.sumComm_apply]
      change q.symm (coord K (Fin (c+d)) (fun _ => p)
        (e.symm ((finSumFinEquiv.symm (Fin.castAdd d i)).swap)))=_
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    · apply congrArg List.ofFn
      funext i
      simp only [AlgEquiv.trans_apply,E,reindexEquiv_coord,perm,Equiv.trans_apply,
        finSumFinEquiv_symm_apply_natAdd,Equiv.sumComm_apply,
        Equiv.symm_trans_apply,Equiv.sumComm_symm]
  change FrobeniusTruncation.residue K (Fin (c+d)) p _
    (topCoefficient K (Ring K (Fin (c+d)) (fun _ => p)) (c+d)
      (normalCycle K (Ring K (Fin (c+d)) (fun _ => p)) (Fin (c+d))
        (chartDerivative K K (Fin (c+d)) p) p
        (List.ofFn (fun i => (E.trans q.symm) (coord K (Fin (c+d)) (fun _ => p) i)))))≠0 at hn
  rw [hlist,normalCycle_append] at hn
  exact hn

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.Forms
noncomputable section
open scoped TensorProduct
variable (K A B σ τ : Type*) [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Fintype σ] [DecidableEq σ]
  [Fintype τ] [DecidableEq τ]

theorem reindexForms_normalCycle (e : σ ≃ τ) (f : A ≃ₐ[K] B)
    (derA : σ → A →ₗ[K] A) (derB : τ → B →ₗ[K] B)
    (hder : ∀ i a, derB (e i) (f a)=f (derA i a)) (p : ℕ) (cs : List A) :
    reindexForms K A B σ τ e f (normalCycle K A σ derA p cs)=
      normalCycle K B τ derB p (cs.map f) := by
  simp only [normalCycle,map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp_apply,normalFactor,map_mul,reindexForms_scalar,map_pow,
    reindexForms_differential K A B σ τ e f derA derB hder]

end
end PD4Tensor.Forms

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open PD4Tensor.Forms
variable (R σ τ : Type*) [CommRing R] (p : ℕ)

@[simp] theorem renameHom_mk (e : σ → τ) (a : MvPolynomial σ R) :
    renameHom R σ τ p e (Ideal.Quotient.mk (ideal R σ (fun _ => p)) a)=
      Ideal.Quotient.mk (ideal R τ (fun _ => p)) (MvPolynomial.rename e a) := by
  induction a using MvPolynomial.induction_on with
  | C a =>
    change renameHom R σ τ p e (algebraMap R _ a)=_
    rw [AlgHom.commutes,MvPolynomial.rename_C]
    rfl
  | add a b ha hb => simp only [map_add,ha,hb]
  | mul_X a i ha =>
    simp only [map_mul,MvPolynomial.rename_X]
    change renameHom R σ τ p e (Ideal.Quotient.mk _ a) *
      renameHom R σ τ p e (coord R σ (fun _ => p) i)=_
    rw [ha,renameHom_coord]
    rfl

variable [CharP R p]
theorem reindexEquiv_partial (e : σ ≃ τ) (i : σ) (a : Ring R σ (fun _ => p)) :
    relativeDeriv R τ p (e i) (reindexEquiv R σ τ p e a)=
      reindexEquiv R σ τ p e (relativeDeriv R σ p i a) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  change relativeDeriv R τ p (e i) (renameHom R σ τ p e (Ideal.Quotient.mk _ a))=
    renameHom R σ τ p e (relativeDeriv R σ p i (Ideal.Quotient.mk _ a))
  simp only [renameHom_mk,partial_mk,MvPolynomial.pderiv_rename e.injective]

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open PD4Tensor.Forms
variable (K υ τ : Type*) [Field K] [Fintype υ] [DecidableEq υ]
  [Fintype τ] [DecidableEq τ] (p : ℕ) [CharP K p]
  {σ : Type*} {c : ℕ}

def reindexChart (e : υ ≃ τ)
    (q : Ring K υ (fun _ => p) ≃ₐ[K] Ring K υ (fun _ => p)) :
    Ring K τ (fun _ => p) ≃ₐ[K] Ring K τ (fun _ => p) :=
  (reindexEquiv K υ τ p e).symm.trans (q.trans (reindexEquiv K υ τ p e))

theorem chartNormal_reindex [Invertible (2 : K)] (r : υ ≃ τ) (e : υ ≃ σ ⊕ Fin c)
    (q : Ring K υ (fun _ => p) ≃ₐ[K] Ring K υ (fun _ => p)) :
    reindexForms K (Ring K υ (fun _ => p)) (Ring K τ (fun _ => p)) υ τ
      r (reindexEquiv K υ τ p r) (chartNormal K K υ p e q)=
    chartNormal K K τ p (r.symm.trans e) (reindexChart K υ τ p r q) := by
  rw [chartNormal,reindexForms_normalCycle K _ _ υ τ r (reindexEquiv K υ τ p r)
    (chartDerivative K K υ p) (chartDerivative K K τ p)
    (reindexEquiv_partial K υ τ p r)]
  change normalCycle K (Ring K τ (fun _ => p)) τ (chartDerivative K K τ p) p _=_
  congr 1
  simp only [normalCoordinates,List.map_ofFn,Function.comp_def]
  congr 1
  funext j
  simp only [reindexChart,AlgEquiv.symm_trans_apply,AlgEquiv.symm_symm,
    Equiv.symm_trans_apply,Equiv.symm_symm,reindexEquiv_symm_coord,Equiv.symm_apply_apply]

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ) [CharP K p]
end
end PD4Tensor.FrobeniusTruncation

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct
open Forms FrobeniusTruncation
variable (K : Type*) [Field K] (N p : ℕ)

theorem residueForm_topCoefficient (hp : 0<p) (ω : Space K (Fin N) p) :
    residueForm K (Fin N) p hp (topExterior K N) ω=
      residue K (Fin N) p hp (topCoefficient K (A K (Fin N) p) N ω) := by
  induction ω using TensorProduct.inductionOn with
  | add ω η hω hη => simp only [map_add,hω,hη]
  | tmul a v =>
    rw [residueForm_tmul,topCoefficient_tmul,map_smul,smul_eq_mul,mul_comm]

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open scoped TensorProduct
open PD4Tensor.Forms PD4Tensor.TruncatedForms
variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ)
  [CharP K p] {N : ℕ}

 

def orientedResidue (hp : 0<p) (r : σ ≃ Fin N) :
    Ω K (Ring K σ (fun _ => p)) σ →ₗ[K] K :=
  (residueForm K (Fin N) p hp (topExterior K N)).comp
    (reindexForms K _ _ σ (Fin N) r (reindexEquiv K σ (Fin N) p r)).toLinearMap

theorem orientedResidue_stokes (hp : 0<p) (r : σ ≃ Fin N)
    (ω : Ω K (Ring K σ (fun _ => p)) σ) :
    orientedResidue K σ p hp r
      (differential K (Ring K σ (fun _ => p)) σ (chartDerivative K K σ p) ω)=0 := by
  change residueForm K (Fin N) p hp (topExterior K N)
    (reindexForms K _ _ σ (Fin N) r (reindexEquiv K σ (Fin N) p r)
      (differential K _ σ (chartDerivative K K σ p) ω))=0
  rw [reindexForms_differential K _ _ σ (Fin N) r (reindexEquiv K σ (Fin N) p r)
      (chartDerivative K K σ p) (chartDerivative K K (Fin N) p)
      (reindexEquiv_partial K σ (Fin N) p r)]
  exact stokes K (Fin N) p hp (topExterior K N) _

theorem orientedResidue_closed_exact (hp : 0<p) (r : σ ≃ Fin N)
    (ω η : Ω K (Ring K σ (fun _ => p)) σ)
    (hω : differential K (Ring K σ (fun _ => p)) σ (chartDerivative K K σ p) ω=0) :
    orientedResidue K σ p hp r
      (ω * differential K (Ring K σ (fun _ => p)) σ (chartDerivative K K σ p) η)=0 := by
  have h := orientedResidue_stokes K σ p hp r (parity K _ σ ω * η)
  rw [differential_mul (chartDerivative K K σ p) (partial_mul K σ p),differential_parity,hω,map_zero,neg_zero,
    zero_mul,zero_add,parity_parity] at h
  exact h

variable [Fact p.Prime] [Invertible (2 : K)] {c d : ℕ}
 

theorem orientedResidue_chartNormal_pair
    (r : σ ≃ Fin (c+d)) (e : σ ≃ Fin d ⊕ Fin c)
    (q : Ring K σ (fun _ => p) ≃ₐ[K] Ring K σ (fun _ => p)) :
    orientedResidue K σ p (Fact.out : p.Prime).pos r
      (chartNormal K K σ p e q * chartNormal K K σ p (e.trans (Equiv.sumComm _ _)) q)≠0 := by
  change residueForm K (Fin (c+d)) p _ (topExterior K (c+d))
    (reindexForms K _ _ σ (Fin (c+d)) r (reindexEquiv K σ (Fin (c+d)) p r)
      (chartNormal K K σ p e q * chartNormal K K σ p (e.trans (Equiv.sumComm _ _)) q))≠0
  rw [map_mul,
    chartNormal_reindex,chartNormal_reindex]
  intro hzero
  apply chartNormal_pair_nonzero K c d p (r.symm.trans e)
    (reindexChart K σ (Fin (c+d)) p r q)
  exact (residueForm_topCoefficient K (c+d) p (Fact.out : p.Prime).pos _).symm.trans hzero

end
end PD4Tensor.FiniteCoordinates
end

end OAI

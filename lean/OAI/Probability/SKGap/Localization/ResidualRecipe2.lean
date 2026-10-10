import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryRecipe
import OAI.Probability.SKGap.Localization.PhiRegularity
import OAI.Probability.SKGap.Localization.ResidualInduction

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace OrdinaryData

lemma evaluation_prefix_eq (D E : OrdinaryData n ι κ σ) (N : ℕ)
    (hJ : E.J=D.J) (hj : E.j=D.j) (hp : E.predecessor=D.predecessor) (hs : E.seed=D.seed)
    (hseed : ∀a≤N,∀s,E.seedCoefficient a s=D.seedCoefficient a s)
    (haux : ∀a≤N,∀b,E.auxCoefficient a b=D.auxCoefficient a b)
    (hseedp : ∀a≤N,∀l s,E.seedPartial a l s=D.seedPartial a l s)
    (hauxp : ∀a≤N,∀l b,E.auxPartial a l b=D.auxPartial a l b) :
    ∀a≤N,E.source a=D.source a ∧ E.auxiliary a=D.auxiliary a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha
    have hy : ∀ b:Fin a, E.auxiliary b=D.auxiliary b := by
      intro b; exact (ih b b.isLt (b.isLt.le.trans ha)).2
    have hw : ∀ b:Fin a, E.source b=D.source b := by
      intro b; exact (ih b b.isLt (b.isLt.le.trans ha)).1
    have hsrc : E.sourceOf a (fun b=>E.auxiliary b)=D.sourceOf a (fun b=>D.auxiliary b) := by
      funext x i
      unfold sourceOf
      simp only [hseed a ha,haux a ha,hs,hy]
    have hpart : ∀l,E.partialOf a l (fun b=>E.auxiliary b)=D.partialOf a l (fun b=>D.auxiliary b) := by
      intro l
      funext x i
      unfold partialOf
      simp only [hseedp a ha,hauxp a ha,hs,hy]
    constructor
    · simpa only [source_eq] using hsrc
    · rw [auxiliary_eq,auxiliary_eq]
      funext x i
      simp only [fieldOf,hJ,hj,hp,hsrc,hpart,hw,haux a ha]

def appendProduct (D : OrdinaryData n ι κ σ) (N : ℕ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ) : OrdinaryData n ι κ σ :=
  { D with
    seedFunction := fun a s i u=>if a=N+1 then F i u*D.seedFunction N s i u else D.seedFunction a s i u
    seedDerivative := fun a s i u=>if a=N+1 then
      F i u • D.seedDerivative N s i u+D.seedFunction N s i u • F' i u else D.seedDerivative a s i u
    auxFunction := fun a b i u=>if a=N+1 then
      if hb:b.val<N then F i u*D.auxFunction N ⟨b.val,hb⟩ i u else 0 else D.auxFunction a b i u
    auxDerivative := fun a b i u=>if a=N+1 then
      if hb:b.val<N then F i u • D.auxDerivative N ⟨b.val,hb⟩ i u+
        D.auxFunction N ⟨b.val,hb⟩ i u • F' i u else 0 else D.auxDerivative a b i u }

lemma appendProduct_prefix (D : OrdinaryData n ι κ σ) (N : ℕ) (F F') :
    ∀a≤N,(D.appendProduct N F F').source a=D.source a ∧
      (D.appendProduct N F F').auxiliary a=D.auxiliary a := by
  apply evaluation_prefix_eq
  · rfl
  · rfl
  · rfl
  · rfl
  all_goals
    intro a ha
    have hn : a≠N+1 := by omega
  · intro s; ext x i; simp [seedCoefficient,coefficient,appendProduct,hn]
  · intro b; ext x i; simp [auxCoefficient,coefficient,appendProduct,hn]
  · intro l s; ext x i; simp [seedPartial,localPartial,appendProduct,hn]
  · intro l b; ext x i; simp [auxPartial,localPartial,appendProduct,hn]

lemma appendProduct_source (D : OrdinaryData n ι κ σ) (N : ℕ) (F F') :
    (D.appendProduct N F F').source (N+1)=
      fun x i=>coefficient D.H D.θ F x i*D.source N x i := by
  have hprev:=D.appendProduct_prefix N F F'
  ext x i
  rw [source_eq]
  dsimp only [sourceOf]
  rw [Fin.sum_univ_castSucc]
  simp only [auxCoefficient,seedCoefficient,coefficient,appendProduct,ite_true,Fin.val_castSucc,
    Fin.val_last,Fin.isLt,dite_true,lt_self_iff_false,dite_false,zero_mul,add_zero]
  have hy : ∀b:Fin N,(D.appendProduct N F F').auxiliary b=D.auxiliary b :=
    fun b=>(hprev b (by omega)).2
  dsimp only [appendProduct] at hy
  simp only [hy,Fin.eta]
  rw [D.source_eq]
  simp only [sourceOf,seedCoefficient,coefficient,auxCoefficient,mul_add,Finset.mul_sum,mul_assoc]

lemma appendProduct_partial (D : OrdinaryData n ι κ σ) (N : ℕ) (F F') (l : ι) :
    (D.appendProduct N F F').sourcePartial (N+1) l=
      fun x i=>coefficient D.H D.θ F x i*D.sourcePartial N l x i+
        localPartial D.H D.θ F' (.inl l) x i*D.source N x i := by
  have hprev:=D.appendProduct_prefix N F F'
  ext x i
  dsimp only [sourcePartial,partialOf]
  rw [Fin.sum_univ_castSucc]
  simp only [auxPartial,seedPartial,localPartial,appendProduct,ite_true,Fin.val_castSucc,
    Fin.val_last,Fin.isLt,dite_true,lt_self_iff_false,dite_false]
  have hy : ∀b:Fin N,(D.appendProduct N F F').auxiliary b=D.auxiliary b :=
    fun b=>(hprev b (by omega)).2
  dsimp only [appendProduct] at hy
  simp only [hy,Fin.eta]
  rw [D.source_eq]
  simp only [sourceOf,seedCoefficient,coefficient,auxCoefficient,partialAt,add_apply,
    smul_apply,smul_eq_mul,add_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum,
    zero_apply,zero_mul,add_zero,mul_assoc]
  simp only [mul_assoc,mul_comm,mul_left_comm]
  ring

lemma appendProduct_new_partial (D : OrdinaryData n ι κ σ) (N : ℕ) (F F') (l : ι)
    (hzero : D.sourcePartial N l=0) :
    (D.appendProduct N F F').sourcePartial (N+1) l=
      fun x i=>localPartial D.H D.θ F' (.inl l) x i*D.source N x i := by
  rw [appendProduct_partial,hzero]
  ext x i; simp

end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def phiCoefficient (l m : ι) (α : κ) : Fin n→Args (ι:=ι) (κ:=κ)→ℝ :=
  fun _ u=>eval3 (KernelExpr.atom 0 0 false).eval (phiPairSelect l m α u)
def phiDerivative (l m : ι) (α : κ) : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ :=
  fun _ u=>((KernelExpr.atom 0 0 false).gradient (phiPairSelect l m α u)).comp (phiPairSelect l m α)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma phiCoefficient_eq (l m : ι) (α : κ) (i : Fin n) (u : Args (ι:=ι) (κ:=κ)) :
    phiCoefficient l m α i u=phi (u (.inl l)) (u (.inl m)) (u (.inr α)) := by
  simp [phiCoefficient,eval3,phiPairSelect,KernelExpr.eval,moment_base]

lemma base_dz (z r a : ℝ) : (KernelExpr.atom 0 0 false).dz.eval z r a=phiZ z r a := by
  have H:=(KernelExpr.atom 0 0 false).hasDerivAt_z z r a
  simp only [KernelExpr.eval,moment_base] at H
  exact H.unique (phi_hasDerivAt z r a)

omit [Fintype ι] [Fintype κ] in
lemma phiDerivative_first (l m : ι) (α : κ) (hlm : l≠m) (i : Fin n) (u : Args (ι:=ι) (κ:=κ)) :
    partialAt (phiDerivative l m α i u) (.inl l)=phiZ (u (.inl l)) (u (.inl m)) (u (.inr α)) := by
  simp [partialAt,phiDerivative,phiPairSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,hlm.symm,eval3,base_dz]

omit [Fintype ι] [Fintype κ] in
lemma phiDerivative_other (l m q : ι) (α : κ) (hql : q≠l) (hqm : q≠m)
    (i : Fin n) (u : Args (ι:=ι) (κ:=κ)) :
    partialAt (phiDerivative l m α i u) (.inl q)=0 := by
  simp [partialAt,phiDerivative,phiPairSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,hql.symm,hqm.symm]

namespace OrdinaryData

def appendStein (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ) : OrdinaryData n ι κ σ :=
  D.appendProduct N (phiCoefficient l m α) (phiDerivative l m α)

lemma appendStein_source (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ)
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x)) :
    (D.appendStein N l m α).source (N+1)=steinSource j J h k (D.source N) := by
  rw [appendStein,appendProduct_source]
  ext x i
  simp [coefficient,phiCoefficient_eq,localArgs,hl,hm,ha,steinSource]

lemma appendStein_partial (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ)
    (hlm : l≠m) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x))
    (hzero : D.sourcePartial N l=0) :
    (D.appendStein N l m α).sourcePartial (N+1) l=steinPartial j J h k (D.source N) := by
  rw [appendStein,appendProduct_new_partial _ _ _ _ _ hzero]
  ext x i
  simp [localPartial,phiDerivative_first l m α hlm,localArgs,hl,hm,ha,steinPartial]

lemma appendStein_preserves_vanishing (D : OrdinaryData n ι κ σ) (N : ℕ) (l m q : ι) (α : κ)
    (hql : q≠l) (hqm : q≠m) (hzero : D.sourcePartial N q=0) :
    (D.appendStein N l m α).sourcePartial (N+1) q=0 := by
  rw [appendStein,appendProduct_new_partial _ _ _ _ _ hzero]
  ext x i
  simp only [localPartial,phiDerivative_other l m q α hql hqm,zero_mul,Pi.zero_apply]

lemma sum_split (f : ι→ℝ) (l : ι) : (∑q,f q)=f l+∑q:{q:ι//q≠l},f q := by
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ l),add_comm]
  congr 1
  exact Finset.sum_subtype (Finset.univ.erase l) (fun q=>show q∈Finset.univ.erase l ↔ q≠l by simp) f

lemma auxiliary_split (D : OrdinaryData n ι κ σ) (a : ℕ) (l : ι) (x : Spin n) (i : Fin n) :
    D.auxiliary a x i=(∑b,D.J i b*D.source a x b)-
      D.j*siteMean (D.sourcePartial a l) x*D.predecessor l x i-
      D.j*(∑q:{q:ι//q≠l},siteMean (D.sourcePartial a q) x*D.predecessor q x i)-
      D.j*∑b:Fin a,siteMean (D.auxCoefficient a b) x*D.source b x i := by
  rw [auxiliary_eq]
  simp only [fieldOf,←D.source_eq,sourcePartial,Matrix.mulVec,dotProduct]
  rw [sum_split _ l]
  ring

lemma appendStein_auxiliary (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ)
    (hlm : l≠m) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (L : ι→ℕ) (hj : D.j=j) (hJ : D.J=J)
    (hp : ∀q,D.predecessor q=mag j J h (L q)) (hL : L l=k)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x))
    (hzero : D.sourcePartial N l=0) :
    let E:=D.appendStein N l m α
    E.auxiliary (N+1)=nextField j J h k (D.source N)
      (fun q:{q:ι//q≠l}=>L q) (fun q=>siteMean (E.sourcePartial (N+1) q))
      (fun b:Fin (N+1)=>E.source b) (fun b=>siteMean (E.auxCoefficient (N+1) b)) := by
  dsimp only
  funext x i
  rw [auxiliary_split _ _ l,appendStein_source D N l m α j J h k hl hm ha,
    appendStein_partial D N l m α hlm j J h k hl hm ha hzero]
  simp only [appendStein,appendProduct,hJ,hj,hp,hL,nextField]

theorem residual_step (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ)
    (hlm : l≠m) (hn : 0<n) (j : ℝ) (J : Interaction n) (hJs : J.IsSymm)
    (h : Fin n→ℝ) (k : ℕ) (L : ι→ℕ) (hj : D.j=j) (hJ : D.J=J)
    (hp : ∀q,D.predecessor q=mag j J h (L q)) (hL : L l=k)
    (hl : D.H l=fld j J h k) (hm : D.H m=fld j J h (k+1))
    (ha : D.θ α=fun x=>j*(onsager j J h (k+1) x-onsager j J h k x))
    (hzero : D.sourcePartial N l=0) (x : Spin n) :
    let E:=D.appendStein N l m α
    (∑i,residual j J h (k+1) x i*D.source N x i)=
      (∑i,residual j J h k x i*E.auxiliary (N+1) x i)+
      j*(onsager j J h (k+1) x-onsager j J h k x)*(∑i,residual j J h k x i*E.source (N+1) x i)-
      j*onsager j J h k x*(∑i,previousResidual j J h k x i*E.source (N+1) x i)+
      j*(∑b:Fin (N+1),siteMean (E.auxCoefficient (N+1) b) x*∑i,residual j J h k x i*E.source b x i)+
      j*(∑q:{q:ι//q≠l},siteMean (E.sourcePartial (N+1) q) x*∑i,residual j J h k x i*mag j J h (L q) x i)-
      j*siteMean (E.sourcePartial (N+1) l) x*(∑i,residual j J h k x i*mag j J h (k+1) x i) := by
  dsimp only
  rw [appendStein_auxiliary D N l m α hlm j J h k L hj hJ hp hL hl hm ha hzero,
    appendStein_source D N l m α j J h k hl hm ha,
    appendStein_partial D N l m α hlm j J h k hl hm ha hzero]
  exact residual_induction_identity hn j J hJs h k (D.source N)
    (fun q:{q:ι//q≠l}=>L q)
    (fun q=>siteMean ((D.appendStein N l m α).sourcePartial (N+1) q))
    (fun b:Fin (N+1)=>(D.appendStein N l m α).source b)
    (fun b=>siteMean ((D.appendStein N l m α).auxCoefficient (N+1) b)) x

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI

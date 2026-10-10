import Mathlib
import OAI.Probability.SKGap.Localization.ResidualAdmissibility
import OAI.Probability.SKGap.Localization.StartedRecipe

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma started_evaluation_prefix_eq (D E : OrdinaryData n ι κ σ) (w y : VectorFields n) (N : ℕ)
    (hJ : E.J=D.J) (hj : E.j=D.j) (hp : E.predecessor=D.predecessor) (hs : E.seed=D.seed)
    (hseed : ∀a≤N,∀s,E.seedCoefficient a s=D.seedCoefficient a s)
    (haux : ∀a≤N,∀b,E.auxCoefficient a b=D.auxCoefficient a b)
    (hseedp : ∀a≤N,∀l s,E.seedPartial a l s=D.seedPartial a l s)
    (hauxp : ∀a≤N,∀l b,E.auxPartial a l b=D.auxPartial a l b) :
    ∀a≤N,E.startedSource w y a=D.startedSource w y a ∧ E.startedAuxiliary w y a=D.startedAuxiliary w y a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha
    by_cases hzero:a=0
    · subst a; simp
    have hapos:0<a:=by omega
    have hy : ∀ b:Fin a, E.startedAuxiliary w y b=D.startedAuxiliary w y b := by
      intro b; exact (ih b b.isLt (b.isLt.le.trans ha)).2
    have hw : ∀ b:Fin a, E.startedSource w y b=D.startedSource w y b := by
      intro b; exact (ih b b.isLt (b.isLt.le.trans ha)).1
    have hsrc : E.sourceOf a (fun b=>E.startedAuxiliary w y b)=D.sourceOf a (fun b=>D.startedAuxiliary w y b) := by
      funext x i
      unfold sourceOf
      simp only [hseed a ha,haux a ha,hs,hy]
    have hpart : ∀l,E.partialOf a l (fun b=>E.startedAuxiliary w y b)=D.partialOf a l (fun b=>D.startedAuxiliary w y b) := by
      intro l
      funext x i
      unfold partialOf
      simp only [hseedp a ha,hauxp a ha,hs,hy]
    constructor
    · simpa only [startedSource_eq _ _ _ hapos] using hsrc
    · rw [startedAuxiliary_eq _ _ _ hapos,startedAuxiliary_eq _ _ _ hapos]
      funext x i
      simp only [fieldOf,hJ,hj,hp,hsrc,hpart,hw,haux a ha]

lemma appendProduct_started_prefix (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (N : ℕ) (F F') :
    ∀a≤N,(D.appendProduct N F F').startedSource w y a=D.startedSource w y a ∧
      (D.appendProduct N F F').startedAuxiliary w y a=D.startedAuxiliary w y a := by
  apply started_evaluation_prefix_eq
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

lemma appendProduct_started_source (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (N : ℕ) (hN : 0<N) (F F') :
    (D.appendProduct N F F').startedSource w y (N+1)=
      fun x i=>coefficient D.H D.θ F x i*D.startedSource w y N x i := by
  have hprev:=D.appendProduct_started_prefix w y N F F'
  ext x i
  rw [startedSource_eq _ _ _ (by omega)]
  dsimp only [sourceOf]
  rw [Fin.sum_univ_castSucc]
  simp only [auxCoefficient,seedCoefficient,coefficient,appendProduct,ite_true,Fin.val_castSucc,
    Fin.val_last,Fin.isLt,dite_true,lt_self_iff_false,dite_false,zero_mul,add_zero]
  have hy : ∀b:Fin N,(D.appendProduct N F F').startedAuxiliary w y b=D.startedAuxiliary w y b :=
    fun b=>(hprev b (by omega)).2
  dsimp only [appendProduct] at hy
  simp only [hy,Fin.eta]
  rw [D.startedSource_eq w y hN]
  simp only [sourceOf,seedCoefficient,coefficient,auxCoefficient,mul_add,Finset.mul_sum,mul_assoc]

lemma appendProduct_started_partial (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (N : ℕ) (hN : 0<N) (F F') (l : ι) :
    (D.appendProduct N F F').startedPartial w y (N+1) l=
      fun x i=>coefficient D.H D.θ F x i*D.startedPartial w y N l x i+
        localPartial D.H D.θ F' (.inl l) x i*D.startedSource w y N x i := by
  have hprev:=D.appendProduct_started_prefix w y N F F'
  ext x i
  dsimp only [startedPartial,partialOf]
  rw [Fin.sum_univ_castSucc]
  simp only [auxPartial,seedPartial,localPartial,appendProduct,ite_true,Fin.val_castSucc,
    Fin.val_last,Fin.isLt,dite_true,lt_self_iff_false,dite_false]
  have hy : ∀b:Fin N,(D.appendProduct N F F').startedAuxiliary w y b=D.startedAuxiliary w y b :=
    fun b=>(hprev b (by omega)).2
  dsimp only [appendProduct] at hy
  simp only [hy,Fin.eta]
  rw [D.startedSource_eq w y hN]
  simp only [sourceOf,seedCoefficient,coefficient,auxCoefficient,partialAt,add_apply,
    smul_apply,smul_eq_mul,add_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum,
    zero_apply,zero_mul,add_zero,mul_assoc]
  simp only [mul_assoc,mul_comm,mul_left_comm]
  ring

end SKGapCutoff.Recipe.OrdinaryData

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma appendAuxiliary_started_prefix (D : OrdinaryData n (Fin M) κ σ) (w y : VectorFields n) (N : ℕ) :
    ∀a≤N,(D.appendAuxiliary N).startedSource w y a=D.startedSource w y a ∧
      (D.appendAuxiliary N).startedAuxiliary w y a=D.startedAuxiliary w y a := by
  apply started_evaluation_prefix_eq D (D.appendAuxiliary N) w y N rfl rfl rfl rfl
  all_goals
    intro a ha
    have hh : a≠N+1 := by omega
    simp [seedCoefficient,auxCoefficient,seedPartial,auxPartial,appendAuxiliary,hh]

lemma appendAuxiliary_started_source (D : OrdinaryData n (Fin M) κ σ) (w y : VectorFields n) (N : ℕ) :
    (D.appendAuxiliary N).startedSource w y (N+1)=D.startedAuxiliary w y N := by
  rw [startedSource_eq _ _ _ (by omega)]
  ext x i
  dsimp only [sourceOf]
  rw [Fin.sum_univ_castSucc]
  have hy : (D.appendAuxiliary N).startedAuxiliary w y N=D.startedAuxiliary w y N := (D.appendAuxiliary_started_prefix w y N N le_rfl).2
  dsimp only [appendAuxiliary] at hy
  simp [seedCoefficient,auxCoefficient,coefficient,appendAuxiliary,hy,
    show ∀b:Fin N,b.val≠N from fun b=>Nat.ne_of_lt b.isLt]

lemma Admissible.startedPartial {D : OrdinaryData n (Fin M) κ σ} {N p : ℕ}
    (h : D.Admissible N p) (w y : VectorFields n) (a : ℕ) (ha : a≤N)
    (q : Fin M) (hq : q.val<p) : D.startedPartial w y a q=0 := by
  ext x i
  simp only [OrdinaryData.startedPartial,partialOf,(h a ha q hq).1,(h a ha q hq).2,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI

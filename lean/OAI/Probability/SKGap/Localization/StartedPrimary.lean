import Mathlib
import OAI.Probability.SKGap.Matrix.NormalizedPrimaryRecipe
import OAI.Probability.SKGap.Localization.StartedRecipe

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]

def appendPrimary (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (q : Fin M) :
    OrdinaryData n (Fin M) κ (σ⊕Unit) where
  J:=D.J
  j:=D.j
  H:=D.H
  predecessor:=D.predecessor
  θ:=D.θ
  seed:=Sum.elim D.seed (fun _ _=>(Real.sqrt (n:ℝ))⁻¹)
  seedFunction:=fun a s i u=>if a=N+1 then
    Sum.elim (fun _=>0) (fun _=>Real.tanh (u (.inl q))) s
    else Sum.elim (fun s=>D.seedFunction a s i u) (fun _=>0) s
  seedDerivative:=fun a s i u=>if a=N+1 then
    Sum.elim (fun _=>0) (fun _=>(1-(Real.tanh (u (.inl q)))^2) • ContinuousLinearMap.proj (.inl q)) s
    else Sum.elim (fun s=>D.seedDerivative a s i u) (fun _=>0) s
  auxFunction:=fun a b i u=>if a=N+1 then 0 else D.auxFunction a b i u
  auxDerivative:=fun a b i u=>if a=N+1 then 0 else D.auxDerivative a b i u

lemma appendPrimary_sourceOf (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (q : Fin M)
    (a : ℕ) (ha : a≤N) (Y : Fin a→VectorFields n) :
    (D.appendPrimary N q).sourceOf a Y=D.sourceOf a Y := by
  ext x i
  have hh:a≠N+1:=by omega
  simp [sourceOf,seedCoefficient,auxCoefficient,coefficient,appendPrimary,hh,Fintype.sum_sum_type]

lemma appendPrimary_partialOf (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (q : Fin M)
    (a : ℕ) (ha : a≤N) (l : Fin M) (Y : Fin a→VectorFields n) :
    (D.appendPrimary N q).partialOf a l Y=D.partialOf a l Y := by
  ext x i
  have hh:a≠N+1:=by omega
  simp [partialOf,seedPartial,auxPartial,localPartial,partialAt,appendPrimary,hh,Fintype.sum_sum_type]

lemma appendPrimary_fieldOf (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (q : Fin M)
    (a : ℕ) (ha : a≤N) (W Y : Fin a→VectorFields n) :
    (D.appendPrimary N q).fieldOf a W Y=D.fieldOf a W Y := by
  have hh:a≠N+1:=by omega
  ext x i
  simp only [fieldOf,D.appendPrimary_sourceOf N q a ha,D.appendPrimary_partialOf N q a ha]
  simp only [appendPrimary,auxCoefficient,ite_eq_right hh]

lemma appendPrimary_started_prefix (D : OrdinaryData n (Fin M) κ σ) (w y : VectorFields n)
    (N : ℕ) (q : Fin M) : ∀a≤N,
    (D.appendPrimary N q).startedSource w y a=D.startedSource w y a ∧
    (D.appendPrimary N q).startedAuxiliary w y a=D.startedAuxiliary w y a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih=>
    intro ha
    by_cases hz:a=0
    · subst a;simp
    have hp:0<a:=by omega
    have hs:∀b:Fin a,(D.appendPrimary N q).startedSource w y b=D.startedSource w y b:=
      fun b=>(ih b b.isLt (b.isLt.le.trans ha)).1
    have hf:∀b:Fin a,(D.appendPrimary N q).startedAuxiliary w y b=D.startedAuxiliary w y b:=
      fun b=>(ih b b.isLt (b.isLt.le.trans ha)).2
    constructor
    · rw [startedSource_eq _ _ _ hp,startedSource_eq _ _ _ hp]
      simp only [hf,D.appendPrimary_sourceOf N q a ha]
    · rw [startedAuxiliary_eq _ _ _ hp,startedAuxiliary_eq _ _ _ hp]
      simp only [hs,hf,D.appendPrimary_fieldOf N q a ha]

lemma appendPrimary_started_source (D : OrdinaryData n (Fin M) κ σ) (w y : VectorFields n)
    (N : ℕ) (q : Fin M) : (D.appendPrimary N q).startedSource w y (N+1)=
      fun x i=>Real.tanh (D.H q x i)/Real.sqrt (n:ℝ) := by
  rw [startedSource_eq _ _ _ (by omega)]
  ext x i
  simp [sourceOf,seedCoefficient,auxCoefficient,coefficient,appendPrimary,
    Fintype.sum_sum_type,localArgs,div_eq_mul_inv]

lemma appendPrimary_seed (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (q : Fin M) (hn : 0<n) :
    (∑s,vectorNorm ((D.appendPrimary N q).seed s))=(∑s,vectorNorm (D.seed s))+1 := by
  have hh:=D.normalizedPrimary_seed q hn
  simp only [normalizedPrimary,Finset.univ_unique,Finset.sum_singleton] at hh
  simp only [appendPrimary,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Finset.univ_unique,Finset.sum_singleton,hh]

omit [Fintype σ] in
lemma appendPrimary_Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ) (q : Fin M)
    (hp : p≤q.val) (h : D.Admissible N p) : (D.appendPrimary N q).Admissible (N+1) p := by
  intro a ha l hl
  have hne:l≠q:=by intro he;subst l;omega
  by_cases he:a=N+1
  · subst a
    constructor
    · intro s;cases s <;> ext x i <;>
        simp [seedPartial,localPartial,appendPrimary,partialAt,hne.symm]
    · intro b;ext x i;simp [auxPartial,localPartial,appendPrimary,partialAt]
  · have haN:a≤N:=by omega
    constructor
    · intro s;cases s with
      | inl s=>simpa [seedPartial,localPartial,appendPrimary,he] using (h a haN l hl).1 s
      | inr s=>ext x i;simp [seedPartial,localPartial,appendPrimary,he,partialAt]
    · intro b;simpa [auxPartial,localPartial,appendPrimary,he] using (h a haN l hl).2 b

end SKGapCutoff.Recipe.OrdinaryData

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]

omit [Fintype σ] in
lemma CoefficientClass.appendPrimary {D : OrdinaryData n (Fin M) κ σ} {N : ℕ} {x : Spin n}
    {K : ℝ} (h : D.CoefficientClass N x K) (hK : 2≤K) (q : Fin M) :
    (D.appendPrimary N q).CoefficientClass (N+1) x K := by
  have h0:0≤K:=by linarith [h.one_le]
  refine ⟨h.one_le,?_,?_,?_,?_⟩
  · intro a ha s
    by_cases he:a=N+1
    · subst a;cases s with
      | inl s=>simpa only [OrdinaryData.appendPrimary,ite_eq_left rfl,ite_true,Sum.elim_inl] using
          (segmentRegular_const D.H D.θ x 0).mono h0
      | inr s=>simpa only [OrdinaryData.appendPrimary,ite_eq_left rfl,ite_true,Sum.elim_inr] using
          (tanh_segmentRegular D.H D.θ x q).mono hK
    · cases s with
      | inl s=>simpa only [OrdinaryData.appendPrimary,ite_eq_right he,Sum.elim_inl] using h.seedRegular a (by omega) s
      | inr s=>simpa only [OrdinaryData.appendPrimary,ite_eq_right he,Sum.elim_inr] using
          (segmentRegular_const D.H D.θ x 0).mono h0
  · intro a ha b
    by_cases he:a=N+1
    · subst a;simpa only [OrdinaryData.appendPrimary,ite_eq_left rfl,ite_true] using (segmentRegular_const D.H D.θ x 0).mono h0
    · simpa only [OrdinaryData.appendPrimary,ite_eq_right he] using h.auxRegular a (by omega) b
  · intro a ha s
    by_cases he:a=N+1
    · subst a;cases s with
      | inl s=>intro i k t ht;simpa only [OrdinaryData.appendPrimary,ite_eq_left rfl,ite_true,Sum.elim_inl,abs_zero] using h0
      | inr s=>intro i k t ht
               simpa only [OrdinaryData.appendPrimary,ite_eq_left rfl,ite_true,Sum.elim_inr] using
                 ((tanh_segmentValue D.H D.θ x q) i k t ht).trans hK
    · cases s with
      | inl s=>simpa only [OrdinaryData.appendPrimary,ite_eq_right he,Sum.elim_inl] using h.seedValue a (by omega) s
      | inr s=>intro i k t ht;simpa only [OrdinaryData.appendPrimary,ite_eq_right he,Sum.elim_inr,abs_zero] using h0
  · intro a ha b
    by_cases he:a=N+1
    · subst a;intro i k t ht;simpa only [OrdinaryData.appendPrimary,ite_eq_left rfl,ite_true,abs_zero] using h0
    · simpa only [OrdinaryData.appendPrimary,ite_eq_right he] using h.auxValue a (by omega) b

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI

import Mathlib
import OAI.Probability.SKGap.Localization.RecipeCoefficientClosure
import OAI.Probability.SKGap.Localization.StartedRecipe

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]

def appendFixed (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (v : Fin n→ℝ) :
    OrdinaryData n (Fin M) κ (σ⊕Unit) where
  J:=D.J
  j:=D.j
  H:=D.H
  predecessor:=D.predecessor
  θ:=D.θ
  seed:=Sum.elim D.seed (fun _=>v)
  seedFunction:=fun a s i u=>if a=N+1 then
    Sum.elim (fun _=>0) (fun _=>1) s
    else Sum.elim (fun s=>D.seedFunction a s i u) (fun _=>0) s
  seedDerivative:=fun a s i u=>if a=N+1 then
    Sum.elim (fun _=>0) (fun _=>0) s
    else Sum.elim (fun s=>D.seedDerivative a s i u) (fun _=>0) s
  auxFunction:=fun a b i u=>if a=N+1 then 0 else D.auxFunction a b i u
  auxDerivative:=fun a b i u=>if a=N+1 then 0 else D.auxDerivative a b i u

lemma appendFixed_sourceOf (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (v : Fin n→ℝ)
    (a : ℕ) (ha : a≤N) (Y : Fin a→VectorFields n) :
    (D.appendFixed N v).sourceOf a Y=D.sourceOf a Y := by
  ext x i
  have hh:a≠N+1:=by omega
  simp [sourceOf,seedCoefficient,auxCoefficient,coefficient,appendFixed,hh,Fintype.sum_sum_type]

lemma appendFixed_partialOf (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (v : Fin n→ℝ)
    (a : ℕ) (ha : a≤N) (l : Fin M) (Y : Fin a→VectorFields n) :
    (D.appendFixed N v).partialOf a l Y=D.partialOf a l Y := by
  ext x i
  have hh:a≠N+1:=by omega
  simp [partialOf,seedPartial,auxPartial,localPartial,partialAt,appendFixed,hh,Fintype.sum_sum_type]

lemma appendFixed_fieldOf (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (v : Fin n→ℝ)
    (a : ℕ) (ha : a≤N) (W Y : Fin a→VectorFields n) :
    (D.appendFixed N v).fieldOf a W Y=D.fieldOf a W Y := by
  have hh:a≠N+1:=by omega
  ext x i
  simp only [fieldOf,D.appendFixed_sourceOf N v a ha,D.appendFixed_partialOf N v a ha]
  simp only [appendFixed,auxCoefficient,ite_eq_right hh]

lemma appendFixed_started_prefix (D : OrdinaryData n (Fin M) κ σ) (w y : VectorFields n)
    (N : ℕ) (v : Fin n→ℝ) : ∀a≤N,
    (D.appendFixed N v).startedSource w y a=D.startedSource w y a ∧
    (D.appendFixed N v).startedAuxiliary w y a=D.startedAuxiliary w y a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih=>
    intro ha
    by_cases hz:a=0
    · subst a;simp
    have hp:0<a:=by omega
    have hs:∀b:Fin a,(D.appendFixed N v).startedSource w y b=D.startedSource w y b:=
      fun b=>(ih b b.isLt (b.isLt.le.trans ha)).1
    have hf:∀b:Fin a,(D.appendFixed N v).startedAuxiliary w y b=D.startedAuxiliary w y b:=
      fun b=>(ih b b.isLt (b.isLt.le.trans ha)).2
    constructor
    · rw [startedSource_eq _ _ _ hp,startedSource_eq _ _ _ hp]
      simp only [hf,D.appendFixed_sourceOf N v a ha]
    · rw [startedAuxiliary_eq _ _ _ hp,startedAuxiliary_eq _ _ _ hp]
      simp only [hs,hf,D.appendFixed_fieldOf N v a ha]

lemma appendFixed_started_source (D : OrdinaryData n (Fin M) κ σ) (w y : VectorFields n)
    (N : ℕ) (v : Fin n→ℝ) : (D.appendFixed N v).startedSource w y (N+1)=
      fun _=>v := by
  rw [startedSource_eq _ _ _ (by omega)]
  ext x i
  simp [sourceOf,seedCoefficient,auxCoefficient,coefficient,appendFixed,
    Fintype.sum_sum_type,localArgs]

lemma appendFixed_seed (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (v : Fin n→ℝ) :
    (∑s,vectorNorm ((D.appendFixed N v).seed s))=(∑s,vectorNorm (D.seed s))+vectorNorm v := by
  simp [appendFixed,Fintype.sum_sum_type]

omit [Fintype σ] in
lemma appendFixed_Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ) (v : Fin n→ℝ)
    (h : D.Admissible N p) : (D.appendFixed N v).Admissible (N+1) p := by
  intro a ha l hl
  by_cases he:a=N+1
  · subst a
    constructor <;> intro s
    · cases s <;> ext x i <;>
        simp [seedPartial,localPartial,appendFixed,partialAt]
    · ext x i;simp [auxPartial,localPartial,appendFixed,partialAt]
  · have haN:a≤N:=by omega
    constructor
    · intro s;cases s with
      | inl s=>simpa [seedPartial,localPartial,appendFixed,he] using (h a haN l hl).1 s
      | inr s=>ext x i;simp [seedPartial,localPartial,appendFixed,he,partialAt]
    · intro b;simpa [auxPartial,localPartial,appendFixed,he] using (h a haN l hl).2 b

end SKGapCutoff.Recipe.OrdinaryData

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]

omit [Fintype σ] in
lemma CoefficientClass.appendFixed {D : OrdinaryData n (Fin M) κ σ} {N : ℕ} {x : Spin n}
    {K : ℝ} (h : D.CoefficientClass N x K) (hK : 1≤K) (v : Fin n→ℝ) :
    (D.appendFixed N v).CoefficientClass (N+1) x K := by
  have h0:0≤K:=by linarith [h.one_le]
  refine ⟨h.one_le,?_,?_,?_,?_⟩
  · intro a ha s
    by_cases he:a=N+1
    · subst a;cases s with
      | inl s=>simpa only [OrdinaryData.appendFixed,ite_eq_left rfl,ite_true,Sum.elim_inl] using
          (segmentRegular_const D.H D.θ x 0).mono h0
      | inr s=>simpa only [OrdinaryData.appendFixed,ite_eq_left rfl,ite_true,Sum.elim_inr] using
          (segmentRegular_const D.H D.θ x 1).mono h0
    · cases s with
      | inl s=>simpa only [OrdinaryData.appendFixed,ite_eq_right he,Sum.elim_inl] using h.seedRegular a (by omega) s
      | inr s=>simpa only [OrdinaryData.appendFixed,ite_eq_right he,Sum.elim_inr] using
          (segmentRegular_const D.H D.θ x 0).mono h0
  · intro a ha b
    by_cases he:a=N+1
    · subst a;simpa only [OrdinaryData.appendFixed,ite_eq_left rfl,ite_true] using (segmentRegular_const D.H D.θ x 0).mono h0
    · simpa only [OrdinaryData.appendFixed,ite_eq_right he] using h.auxRegular a (by omega) b
  · intro a ha s
    by_cases he:a=N+1
    · subst a;cases s with
      | inl s=>intro i k t ht;simpa only [OrdinaryData.appendFixed,ite_eq_left rfl,ite_true,Sum.elim_inl,abs_zero] using h0
      | inr s=>intro i k t ht
               simpa only [OrdinaryData.appendFixed,ite_eq_left rfl,ite_true,Sum.elim_inr] using
                 (show |(1:ℝ)|≤K by simpa using hK)
    · cases s with
      | inl s=>simpa only [OrdinaryData.appendFixed,ite_eq_right he,Sum.elim_inl] using h.seedValue a (by omega) s
      | inr s=>intro i k t ht;simpa only [OrdinaryData.appendFixed,ite_eq_right he,Sum.elim_inr,abs_zero] using h0
  · intro a ha b
    by_cases he:a=N+1
    · subst a;intro i k t ht;simpa only [OrdinaryData.appendFixed,ite_eq_left rfl,ite_true,abs_zero] using h0
    · simpa only [OrdinaryData.appendFixed,ite_eq_right he] using h.auxValue a (by omega) b

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI

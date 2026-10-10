import OAI.Combinatorics.ContingencyTables.Transport.IntegerAuxiliaryEnumeration
import OAI.Combinatorics.ContingencyTables.Rooted.LargePairEnumeration

namespace OAI

/-! # The unique excess pair in physical finite coordinates -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration LargePairEnumeration IntegerMarginal

lemma coordinateEquiv_symm_root_succ {S : Type*} {n : ℕ} (M : Fin (n+1) → ℕ) (s : S) :
    (coordinateEquiv S M).symm.toFun (Sum.inl s)=
      Sum.inl ((coordinateEquiv S (fun i => M i.succ)).symm (Sum.inl s)) := rfl

lemma coordinateEquiv_symm_zero {S : Type*} {n : ℕ} (M : Fin (n+1) → ℕ) (b : Bool) :
    (coordinateEquiv S M).symm.toFun (Sum.inr (0,b))=Sum.inr b := rfl

lemma coordinateEquiv_symm_succ {S : Type*} {n : ℕ} (M : Fin (n+1) → ℕ)
    (i : Fin n) (b : Bool) :
    (coordinateEquiv S M).symm.toFun (Sum.inr (i.succ,b))=
      Sum.inl ((coordinateEquiv S (fun j => M j.succ)).symm (Sum.inr (i,b))) := rfl

lemma embedding_root {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (q : Assignments (widths M)) (s : S) :
    embedding (widths M) z q ((coordinateEquiv S M).symm (.inl s))=z s := by
  have h := embedding_coordinate M z ((assignmentEquiv M) q)
    ((coordinateEquiv S M).symm (.inl s))
  simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,joinedProfile] using h

lemma embedding_pair_total {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (q : Assignments (widths M)) (i : Fin n) :
    embedding (widths M) z q ((coordinateEquiv S M).symm (.inr (i,false)))+
      embedding (widths M) z q ((coordinateEquiv S M).symm (.inr (i,true)))=M i := by
  have hfalse := embedding_coordinate M z ((assignmentEquiv M) q)
    ((coordinateEquiv S M).symm (.inr (i,false)))
  have htrue := embedding_coordinate M z ((assignmentEquiv M) q)
    ((coordinateEquiv S M).symm (.inr (i,true)))
  simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,joinedProfile,
    Bool.false_eq_true,↓reduceIte] at hfalse htrue
  rw [hfalse,htrue]
  have hb := ((assignmentEquiv M) q i).isLt
  omega

def excessIndex : {n : ℕ} → (M : Fin n → ℕ) → ExcessAssignments (widths M) → Fin n
  | 0,_,q => Empty.elim q
  | _+1,_,.inl _ => 0
  | _+1,M,.inr q => (excessIndex (fun i => M i.succ) q.1).succ

lemma excessEmbedding_root {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (q : ExcessAssignments (widths M)) (s : S) :
    excessEmbedding (widths M) z q ((coordinateEquiv S M).symm (.inl s))=z s := by
  induction n with
  | zero => exact Empty.elim q
  | succ n ih =>
    cases q with
    | inl q =>
      change embedding (widths (fun i => M i.succ)) z q.1
        ((coordinateEquiv S (fun i => M i.succ)).symm (.inl s))=z s
      exact embedding_root (fun i => M i.succ) z q.1 s
    | inr q =>
      change excessEmbedding (widths (fun i => M i.succ)) z q.1
        ((coordinateEquiv S (fun i => M i.succ)).symm (.inl s))=z s
      exact ih (fun i => M i.succ) q.1

/-- The raw finite profile recovers the distinguished position by its
pair total; all other pairs have their original total. -/
lemma excessEmbedding_pair_total {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (q : ExcessAssignments (widths M)) (i : Fin n) :
    excessEmbedding (widths M) z q ((coordinateEquiv S M).symm (.inr (i,false)))+
      excessEmbedding (widths M) z q ((coordinateEquiv S M).symm (.inr (i,true)))=
      M i+if i=excessIndex M q then 1 else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases q with
    | inl q =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change q.2.val+(M 0+1-q.2.val)=M 0+if (0 : Fin (n+1))=0 then 1 else 0
        have hb := q.2.isLt
        simp only [↓reduceIte]
        omega
      · change embedding (widths (fun j => M j.succ)) z q.1
            ((coordinateEquiv S (fun j => M j.succ)).symm (.inr (j,false)))+
          embedding (widths (fun j => M j.succ)) z q.1
            ((coordinateEquiv S (fun j => M j.succ)).symm (.inr (j,true)))=M j.succ+if j.succ=0 then 1 else 0
        rw [embedding_pair_total]
        simp only [Fin.succ_ne_zero,↓reduceIte,add_zero]
    | inr q =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change q.2.val+(M 0-q.2.val)=M 0+
          if (0 : Fin (n+1))=(excessIndex (fun j => M j.succ) q.1).succ then 1 else 0
        have hb := q.2.isLt
        have hn : (0 : Fin (n+1))≠(excessIndex (fun j => M j.succ) q.1).succ :=
          (Fin.succ_ne_zero _).symm
        simp only [hn,↓reduceIte,add_zero]
        omega
      · change excessEmbedding (widths (fun j => M j.succ)) z q.1
            ((coordinateEquiv S (fun j => M j.succ)).symm (.inr (j,false)))+
          excessEmbedding (widths (fun j => M j.succ)) z q.1
            ((coordinateEquiv S (fun j => M j.succ)).symm (.inr (j,true)))=M j.succ+
          if j.succ=(excessIndex (fun j => M j.succ) q.1).succ then 1 else 0
        rw [ih]
        simp only [Fin.succ_inj]

end ContingencyTables.IntegerWeightedTransport

end OAI

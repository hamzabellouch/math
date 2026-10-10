import Mathlib
import OAI.Computability.MinUncut.Estimates.ExpressionOutput

namespace OAI

section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.Costed
open scoped BigOperators

def keyTag {u : ℕ} : LocalKey u → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def keyTable {u : ℕ} : LocalKey u → ℕ
  | .inl f => (((iEncoding u).function Encoding.bool).code f).val
  | .inr (.inl g) => (((jEncoding u).function Encoding.bool).code g).val
  | .inr (.inr _) => 0

def keyNumber {u : ℕ} (N M c v : ℕ) (x : LocalKey u) : ℕ :=
  if keyTag x=0 then keyTable x+2^(2^u)*v else
  if keyTag x=1 then N^u*2^(2^u)+(keyTable x+2^(8^u)*c) else
    N^u*2^(2^u)+M^u*2^(8^u)

lemma keyAddress_number (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (x : LocalKey u) :
    (keyAddress F c v x).val=keyNumber F.«variables» F.clauses.length
      ((clauseEncoding F u).code c).val ((variableEncoding F u).code v).val x := by
  cases x with
  | inl f => rfl
  | inr x =>
    cases x with
    | inl g => rfl
    | inr z => cases z; rfl

def signatureEquiv (u : ℕ) : Signature u ≃
    (Fin u → Slot → Bool) × ((Fin u × Slot) → (Fin u × Slot) → Bool) where
  toFun s := (s.positive,s.same)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def coordinateEncoding (u : ℕ) : Encoding (Fin u × Slot) := (Encoding.fin u).prod slotEncoding

def signatureEncoding (u : ℕ) : Encoding (Signature u) :=
  let p := (Encoding.fin u).function (slotEncoding.function Encoding.bool)
  let s := (coordinateEncoding u).function ((coordinateEncoding u).function Encoding.bool)
  ⟨(p.prod s).size,(signatureEquiv u).trans (p.prod s).code⟩

def inputTuple (F : Formula) {u : ℕ} (c : ClauseContext F u) : List ℕ :=
  ((clauseEncoding F u).code c).val::Complexity.formulaWords F

def tupleDigit (i : ℕ) : AExpr := .mod (.div (.reg 0) ((AExpr.reg 2).pow i)) (.reg 2)
def slotWord (i : ℕ) (s : Slot) (p : ℕ) : AExpr :=
  .at (.add (.add (.const 3) (.mul (.const 6) (tupleDigit i)))
    (.const (2*(slotEncoding.code s).val+p)))

lemma tupleDigit_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) (i : Fin u) :
    (tupleDigit i.val).eval (inputTuple F c)=(c i).val := by
  have h := congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply c) i)
  have he : (clauseEncoding F u).code c=finFunctionFinEquiv c := by
    apply congrArg finFunctionFinEquiv
    funext j
    rfl
  simp only [tupleDigit,AExpr.eval,AExpr.eval_pow,inputTuple,Complexity.formulaWords,
    List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.headI_cons,he]
  exact h

lemma formula_name_word (F : Formula) (i : Fin F.clauses.length) (s : Slot) :
    ((Complexity.formulaWords F).drop (2+6*i.val+2*(slotEncoding.code s).val)).headI=
      (nameAt (clauseAt F i) s).val := by
  have h : ∀ (xs : List (Clause F.«variables»)) (j : ℕ) (hj : j<xs.length),
      ((xs.flatMap Complexity.clauseWords).drop (6*j+2*(slotEncoding.code s).val)).headI=
        (nameAt xs[j] s).val := by
    intro xs
    induction xs with
    | nil => intro j hj; simp at hj
    | cons e es ih =>
      intro j hj
      cases j with
      | zero => cases s <;> rfl
      | succ j =>
        have he : 6*(j+1)+2*(slotEncoding.code s).val=
            ((((((6*j+2*(slotEncoding.code s).val)+1)+1)+1)+1)+1)+1 := by omega
        rw [he]
        simpa only [List.flatMap_cons,Complexity.clauseWords,Complexity.literalWords,
          List.cons_append,List.nil_append,List.drop_succ_cons,List.getElem_cons_succ] using
          ih j (by simpa using hj)
  have he : 2+6*i.val+2*(slotEncoding.code s).val=(6*i.val+2*(slotEncoding.code s).val)+1+1 := by omega
  rw [he]
  exact h F.clauses i.val i.isLt

lemma formula_positive_word (F : Formula) (i : Fin F.clauses.length) (s : Slot) :
    ((Complexity.formulaWords F).drop (2+6*i.val+(2*(slotEncoding.code s).val+1))).headI=
      (positiveAt (clauseAt F i) s).toNat := by
  have h : ∀ (xs : List (Clause F.«variables»)) (j : ℕ) (hj : j<xs.length),
      ((xs.flatMap Complexity.clauseWords).drop (6*j+(2*(slotEncoding.code s).val+1))).headI=
        (positiveAt xs[j] s).toNat := by
    intro xs
    induction xs with
    | nil => intro j hj; simp at hj
    | cons e es ih =>
      intro j hj
      cases j with
      | zero =>
        cases s with
        | first => change (if e[0].positive then 1 else 0)=e[0].positive.toNat
                   cases e[0].positive <;> rfl
        | second => change (if e[1].positive then 1 else 0)=e[1].positive.toNat
                    cases e[1].positive <;> rfl
        | third => change (if e[2].positive then 1 else 0)=e[2].positive.toNat
                   cases e[2].positive <;> rfl
      | succ j =>
        have he : 6*(j+1)+(2*(slotEncoding.code s).val+1)=
            ((((((6*j+(2*(slotEncoding.code s).val+1))+1)+1)+1)+1)+1)+1 := by omega
        rw [he]
        simpa only [List.flatMap_cons,Complexity.clauseWords,Complexity.literalWords,
          List.cons_append,List.nil_append,List.drop_succ_cons,List.getElem_cons_succ] using
          ih j (by simpa using hj)
  have he : 2+6*i.val+(2*(slotEncoding.code s).val+1)=
      (6*i.val+(2*(slotEncoding.code s).val+1))+1+1 := by omega
  rw [he]
  exact h F.clauses i.val i.isLt

lemma slotWord_name (F : Formula) {u : ℕ} (c : ClauseContext F u) (i : Fin u) (s : Slot) :
    (slotWord i.val s 0).eval (inputTuple F c)=(nameAt (clauseAt F (c i)) s).val := by
  simp only [slotWord,AExpr.eval,tupleDigit_eval,Nat.add_zero]
  have he : 3+6*(c i).val+2*(slotEncoding.code s).val=
      (2+6*(c i).val+2*(slotEncoding.code s).val)+1 := by omega
  rw [he]
  exact formula_name_word F (c i) s

lemma slotWord_positive (F : Formula) {u : ℕ} (c : ClauseContext F u) (i : Fin u) (s : Slot) :
    (slotWord i.val s 1).eval (inputTuple F c)=(positiveAt (clauseAt F (c i)) s).toNat := by
  simp only [slotWord,AExpr.eval,tupleDigit_eval]
  have he : 3+6*(c i).val+(2*(slotEncoding.code s).val+1)=
      (2+6*(c i).val+(2*(slotEncoding.code s).val+1))+1 := by omega
  rw [he]
  exact formula_positive_word F (c i) s

end MinUncut.SourceTemplate

end

end OAI

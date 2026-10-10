import OAI.NumberTheory.Ostmann.Arithmetic.HistoryOccurrenceRows
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportRename

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding
open Arithmetic.HistorySymbolicState Arithmetic.HistorySymbolicSlots Arithmetic.HistoryNumeratorForms
open Characters.RationalHistory

variable {ι κ : Type}

def fixedNodeNumerator (v w : ℤ) (halfLength : ℕ) (split : List ℕ) (e : StateCode ι) : Expr ι :=
  Arithmetic.HistorySymbolicNumerator.numeratorExpr v w e.plus e.minus
    ((select (.fixed 0) split e.small).take halfLength)
    ((select (.fixed 0) split e.small).drop halfLength)

def fixedRows (seed : List SourceSlot) : {l:ℕ}→Plan l→TreeCode ι l→TreeCode ι l→
    Internal seed l→Expr ι×Expr ι
  | _,.leaf _,_,_ => fun i => nomatch i
  | _,.node _ v w n split _ _ left right,c,d =>
      Sum.elim (fun _ => (fixedNodeNumerator v w n split c.1,fixedNodeNumerator v w n split d.1))
        (Sum.elim (fixedRows seed left c.2.1 d.2.1) (fixedRows seed right c.2.2 d.2.2))

lemma nodeNumerator_code {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) (e : StateExpr a ι) :
    nodeNumerator hs e=fixedNodeNumerator left.root.frequency right.root.frequency hp.length
      (permutationOrder (History.supported_small_split hs)) (stateCode e) := by
  simp only [nodeNumerator,fixedNodeNumerator,stateCode,leftPart_code,rightPart_code,splitSlots,reorder_code]

theorem rows_eq_fixedRows (seed : List SourceSlot) {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (hs : h.Supported V outside)
    (c d : TreeExpr ι h) (i : Internal seed l) :
    Arithmetic.HistoryOccurrenceRows.rows V outside h hs c d (internalEquiv seed h hh i)=
      fixedRows seed (plan h hs) (treeCode h c) (treeCode h d) i := by
  induction h with
  | leaf a => exact Empty.elim i
  | node a p u hp hm left right ihl ihr =>
    rcases i with i | i | i
    · simp only [Arithmetic.HistoryOccurrenceRows.rows,internalEquiv,Equiv.sumCongr_apply,Sum.map_inl,Sum.elim_inl,
        fixedRows,plan,treeCode,nodeNumerator_code]
    · exact ihl hh.2.2.2.2.1 (History.supported_left hs) c.2.1 d.2.1 i
    · exact ihr hh.2.2.2.2.2 (History.supported_right hs) c.2.2 d.2.2 i

lemma fixedNodeNumerator_rename (f : ι→κ) (v w : ℤ) (n : ℕ) (split : List ℕ) (e : StateCode ι) :
    (fixedNodeNumerator v w n split e).rename f=fixedNodeNumerator v w n split (e.rename f) := by
  simp only [fixedNodeNumerator,Arithmetic.HistorySymbolicNumerator.numeratorExpr,Expr.rename,
    product_rename,StateCode.rename,List.map_take,List.map_drop,select_map]

theorem fixedRows_rename (seed : List SourceSlot) (f : ι→κ) {l : ℕ} (p : Plan l)
    (c d : TreeCode ι l) (i : Internal seed l) :
    ((fixedRows seed p c d i).1.rename f,(fixedRows seed p c d i).2.rename f)=
      fixedRows seed p (renameTree f c) (renameTree f d) i := by
  induction p with
  | leaf s => exact Empty.elim i
  | node s v w n split lo ro left right ihl ihr =>
    rcases i with i | i | i
    · simp only [fixedRows,Sum.elim_inl,renameTree,fixedNodeNumerator_rename]
    · exact ihl c.2.1 d.2.1 i
    · exact ihr c.2.2 d.2.2 i

theorem renamed_rows_eq_fixedRows (seed : List SourceSlot) {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (hs : h.Supported V outside)
    (c d : TreeExpr ι h) (f : ι→κ) (i : Internal seed l) :
    ((Arithmetic.HistoryOccurrenceRows.rows V outside h hs c d (internalEquiv seed h hh i)).1.rename f,
      (Arithmetic.HistoryOccurrenceRows.rows V outside h hs c d (internalEquiv seed h hh i)).2.rename f)=
      fixedRows seed (plan h hs) (renameTree f (treeCode h c)) (renameTree f (treeCode h d)) i := by
  rw [rows_eq_fixedRows seed h hh hs c d i]
  exact fixedRows_rename seed f _ _ _ i

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory
open HistorySymbolicStep HistorySignedDecode HistorySignedNumerators HistoryOccurrenceVariables
open HistorySymbolicEncoding

def Fits : {l : ℕ} → Plan l → History l → Prop
  | _, .leaf s, .leaf a => s=a.frequency
  | _, .node s v w n sp lo ro lp rp, .node a _ u hp hm left right =>
    s=a.frequency ∧ v=left.root.frequency ∧ w=right.root.frequency ∧ n=hp.length ∧
    select 0 sp (a.small.map fun a => (a.value:ℚ))=(hp++hm).map (fun a => (a.value:ℚ)) ∧
    select 0 lo ((u++hp).map fun a => (a.value:ℚ))=left.root.small.map (fun a => (a.value:ℚ)) ∧
    select 0 ro ((u++hm).map fun a => (a.value:ℚ))=right.root.small.map (fun a => (a.value:ℚ)) ∧
    Fits lp left ∧ Fits rp right

theorem execute_rows_actual {ι : Type} (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (p : Plan l) (hf : Fits p h)
    (e : StateCode ι) (comp : InternalKey h→Expr ι) (x : ι→ℚ) (Xp Xm : ℤ)
    (hp : e.plus.rationalEval x=(Xp:ℚ)) (hm : e.minus.rationalEval x=(Xm:ℚ))
    (he : e.small.map (fun e => e.rationalEval x)=h.root.small.map (fun a => (a.value:ℚ)))
    (hc : ∀i,(comp i).rationalEval x=((internalSlot h i).value:ℚ))
    (i : Internal seed l)
    (hi : AncestorIntegralGuard h Xp Xm (internalEquiv seed h hh i)) :
    (fixedRows seed p (execute p e (compensationCode h comp))
      (execute p e (compensationCode h comp)) i).1.rationalEval x=
      (actual h Xp Xm (internalEquiv seed h hh i):ℚ) := by
  induction h generalizing e Xp Xm with
  | leaf a => exact Empty.elim i
  | @node l a pp u hplus hminus left right ihl ihr =>
    cases p with
    | node s v w n sp lo ro lp rp =>
      rcases hf with ⟨rfl,rfl,rfl,rfl,hsp,hlo,hro,hfl,hfr⟩
      let es := select (.fixed 0) sp e.small
      let ep := es.take hplus.length
      let em := es.drop hplus.length
      let ec := List.ofFn (fun i => comp (Sum.inl i))
      have hspl : es.map (fun z => z.rationalEval x)=
          (hplus++hminus).map (fun a => (a.value:ℚ)) := by
        rw [show es=select (.fixed 0) sp e.small from rfl,select_map,he]
        exact hsp
      have hep : ep.map (fun z => z.rationalEval x)=hplus.map (fun a => (a.value:ℚ)) := by
        change (es.take hplus.length).map _ = _
        rw [List.map_take,hspl,←List.map_take,List.take_left]
      have hem : em.map (fun z => z.rationalEval x)=hminus.map (fun a => (a.value:ℚ)) := by
        change (es.drop hplus.length).map _ = _
        rw [List.map_drop,hspl,←List.map_drop,List.drop_left]
      have hec : ec.map (fun z => z.rationalEval x)=u.map (fun a => (a.value:ℚ)) := by
        simp only [ec,List.map_ofFn,Function.comp_def]
        have hv : (fun i : Fin u.length => (comp (.inl i)).rationalEval x)=
            (fun i => ((u.get i).value:ℚ)) := by
          funext i
          exact hc (.inl i)
        rw [hv]
        exact List.ofFn_getElem_eq_map u (fun a => (a.value:ℚ))
      have hel : (select (.fixed 0) lo (ec++ep)).map (fun z => z.rationalEval x)=
          left.root.small.map (fun a => (a.value:ℚ)) := by
        rw [select_map,List.map_append,hec,hep,←List.map_append]
        exact hlo
      have her : (select (.fixed 0) ro (ec++em)).map (fun z => z.rationalEval x)=
          right.root.small.map (fun a => (a.value:ℚ)) := by
        rw [select_map,List.map_append,hec,hem,←List.map_append]
        exact hro
      rcases i with i | i | i
      · change (HistorySymbolicNumerator.numeratorExpr left.root.frequency right.root.frequency
            e.plus e.minus ep em).rationalEval x=_
        simp only [HistorySymbolicNumerator.numeratorExpr,Expr.rationalEval]
        rw [hp,hm,eval_product _ _ _ hep,eval_product _ _ _ hem]
        simp only [actual_node,internalEquiv,Equiv.sumCongr_apply,Sum.map_inl,Sum.elim_inl,
          reversalNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
      · have hpiv := pivot_eval_signed a.frequency left.root.frequency right.root.frequency
          Xp Xm a.small u hplus hminus e.plus e.minus ec ep em x hp hm hec hep hem hi.1 hi.2.1
        exact ihl hh.2.2.2.2.1 lp hfl
          ⟨pivot a.frequency left.root.frequency right.root.frequency e.plus e.minus ec ep em,
            e.plus,select (.fixed 0) lo (ec++ep)⟩
          (fun j => comp (.inr (.inl j))) _ _ hpiv hp hel
          (fun j => hc (.inr (.inl j))) i hi.2.2
      · have hpiv := pivot_eval_signed a.frequency left.root.frequency right.root.frequency
          Xp Xm a.small u hplus hminus e.plus e.minus ec ep em x hp hm hec hep hem hi.1 hi.2.1
        exact ihr hh.2.2.2.2.2 rp hfr
          ⟨pivot a.frequency left.root.frequency right.root.frequency e.plus e.minus ec ep em,
            e.minus,select (.fixed 0) ro (ec++em)⟩
          (fun j => comp (.inr (.inr j))) _ _ hpiv hm her
          (fun j => hc (.inr (.inr j))) i hi.2.2

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI

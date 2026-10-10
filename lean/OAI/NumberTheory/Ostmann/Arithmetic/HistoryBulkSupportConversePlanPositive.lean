import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanEvaluation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory
open HistorySymbolicStep HistorySignedDecode HistoryOccurrenceVariables HistorySymbolicEncoding

variable {ι : Type}

def rootCode : {l : ℕ} → TreeCode ι l → StateCode ι
  | 0,e => e
  | _+1,e => e.1

def TreeCodeGiantsAgree (x : ι → ℚ) :
    {l : ℕ} → TreeCode ι l → SignedHistory l → Prop
  | _,e,.leaf a => e.plus.rationalEval x=(a.giantPlus:ℚ) ∧
      e.minus.rationalEval x=(a.giantMinus:ℚ)
  | _,e,.node a _ _ _ _ left right =>
      e.1.plus.rationalEval x=(a.giantPlus:ℚ) ∧
      e.1.minus.rationalEval x=(a.giantMinus:ℚ) ∧
      TreeCodeGiantsAgree x e.2.1 left ∧ TreeCodeGiantsAgree x e.2.2 right

theorem TreeCodeGiantsAgree.root {x : ι → ℚ} {l : ℕ}
    {e : TreeCode ι l} {h : SignedHistory l} (he : TreeCodeGiantsAgree x e h) :
    (rootCode e).plus.rationalEval x=(h.root.giantPlus:ℚ) ∧
      (rootCode e).minus.rationalEval x=(h.root.giantMinus:ℚ) := by
  cases h
  · exact he
  · exact ⟨he.1,he.2.1⟩

theorem execute_rebuild_giantsAgree {l : ℕ}
    (h : History l) (p : Plan l) (hf : Fits p h)
    (e : StateCode ι) (comp : InternalKey h→Expr ι) (x : ι→ℚ) (Xp Xm : ℤ)
    (hp : e.plus.rationalEval x=(Xp:ℚ)) (hm : e.minus.rationalEval x=(Xm:ℚ))
    (he : e.small.map (fun e => e.rationalEval x)=h.root.small.map (fun a => (a.value:ℚ)))
    (hc : ∀i,(comp i).rationalEval x=((internalSlot h i).value:ℚ))
    (hi : (rebuild h Xp Xm).IntegralGuard) :
    TreeCodeGiantsAgree x (execute p e (compensationCode h comp)) (rebuild h Xp Xm) := by
  induction h generalizing e Xp Xm with
  | leaf a => cases p; exact ⟨hp,hm⟩
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
      have hguard := hi
      simp only [rebuild,SignedHistory.IntegralGuard,rebuild_root] at hguard
      have hpiv := pivot_eval_signed a.frequency left.root.frequency right.root.frequency
        Xp Xm a.small u hplus hminus e.plus e.minus ec ep em x hp hm hec hep hem
        hguard.1 hguard.2.1
      refine ⟨hp,hm,?_,?_⟩
      · exact ihl lp hfl
          ⟨pivot a.frequency left.root.frequency right.root.frequency e.plus e.minus ec ep em,
            e.plus,select (.fixed 0) lo (ec++ep)⟩
          (fun j => comp (.inr (.inl j))) _ _ hpiv hp hel
          (fun j => hc (.inr (.inl j))) hguard.2.2.1
      · exact ihr rp hfr
          ⟨pivot a.frequency left.root.frequency right.root.frequency e.plus e.minus ec ep em,
            e.minus,select (.fixed 0) ro (ec++em)⟩
          (fun j => comp (.inr (.inr j))) _ _ hpiv hm her
          (fun j => hc (.inr (.inr j))) hguard.2.2.2

def CodePivotsPositive (x : ι → ℚ) : {l : ℕ} → TreeCode ι l → Prop
  | 0,_ => True
  | _+1,e => 0 < (rootCode e.2.1).plus.rationalEval x ∧
      CodePivotsPositive x e.2.1 ∧ CodePivotsPositive x e.2.2

theorem TreeCodeGiantsAgree.pivotsPositive_iff {x : ι → ℚ} {l : ℕ}
    (h : History l) (e : TreeCode ι l) (Xp Xm : ℤ)
    (he : TreeCodeGiantsAgree x e (rebuild h Xp Xm)) :
    CodePivotsPositive x e ↔ (rebuild h Xp Xm).PivotsPositive := by
  induction h generalizing Xp Xm with
  | leaf a => rfl
  | node a p u hp hm left right ihl ihr =>
    have hl := he.2.2.1
    have hr := he.2.2.2
    have hpiv := hl.root.1
    rw [rebuild_root] at hpiv
    simp only [CodePivotsPositive,rebuild,SignedHistory.PivotsPositive]
    rw [hpiv]
    exact and_congr Int.cast_pos (and_congr (ihl e.2.1 _ _ hl) (ihr e.2.2 _ _ hr))

theorem execute_pivotsPositive_iff_rebuild {l : ℕ}
    (h : History l) (p : Plan l) (hf : Fits p h)
    (e : StateCode ι) (comp : InternalKey h→Expr ι) (x : ι→ℚ) (Xp Xm : ℤ)
    (hp : e.plus.rationalEval x=(Xp:ℚ)) (hm : e.minus.rationalEval x=(Xm:ℚ))
    (he : e.small.map (fun e => e.rationalEval x)=h.root.small.map (fun a => (a.value:ℚ)))
    (hc : ∀i,(comp i).rationalEval x=((internalSlot h i).value:ℚ))
    (hi : (rebuild h Xp Xm).IntegralGuard) :
    CodePivotsPositive x (execute p e (compensationCode h comp)) ↔
      (rebuild h Xp Xm).PivotsPositive :=
  TreeCodeGiantsAgree.pivotsPositive_iff h _ Xp Xm
    (execute_rebuild_giantsAgree h p hf e comp x Xp Xm hp hm he hc hi)

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI

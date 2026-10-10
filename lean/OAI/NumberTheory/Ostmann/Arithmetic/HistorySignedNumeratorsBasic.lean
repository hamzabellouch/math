import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActualNumerators
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeXi

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedNumerators
open Construction Characters.RationalHistory HistoryOccurrenceVariables HistorySignedDecode
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicSlots HistoryNumeratorForms
open HistoryOccurrenceRows

def signedActual : {l : ℕ} → (h : History l) → SignedHistory l → InternalKey h → ℤ
  | _, .leaf _, .leaf _ => fun i => nomatch i
  | _, .node _ _ _ _ _ left right, .node a _ _ hp hm left' right' =>
    Sum.elim (fun _ => reversalNumerator left'.root.frequency right'.root.frequency
      (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
      (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ)))
      (Sum.elim (signedActual left left') (signedActual right right'))

def actual {l : ℕ} (h : History l) (Xp Xm : ℤ) : InternalKey h → ℤ :=
  signedActual h (rebuild h Xp Xm)

@[simp] theorem actual_node {l : ℕ} (a : State) (p : ℕ) (u hp hm : List SmallSlot)
    (left right : History l) (Xp Xm : ℤ) :
    actual (.node a p u hp hm left right) Xp Xm =
      Sum.elim (fun _ => reversalNumerator left.root.frequency right.root.frequency
        (Xp*((hp.map SmallSlot.value).prod:ℤ)) (Xm*((hm.map SmallSlot.value).prod:ℤ)))
        (Sum.elim
          (actual left (signedPivot ⟨a.frequency,Xp,Xm,a.small⟩
            left.root.frequency right.root.frequency u hp hm) Xp)
          (actual right (signedPivot ⟨a.frequency,Xp,Xm,a.small⟩
            left.root.frequency right.root.frequency u hp hm) Xm)) := by
  simp only [actual,rebuild,signedActual,rebuild_root]

variable {ι : Type*}

theorem nodeNumerator_real_signed {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (x : ι → ℝ) (Xp Xm : ℤ)
    (heplus : e.plus.realEval x = (Xp:ℝ)) (heminus : e.minus.realEval x = (Xm:ℝ))
    (he : SmallRealValues x a.small e.small) :
    (nodeNumerator hs e).realEval x =
      ((reversalNumerator left.root.frequency right.root.frequency
        (Xp*((hp.map SmallSlot.value).prod:ℤ))
        (Xm*((hm.map SmallSlot.value).prod:ℤ)) : ℤ):ℝ) := by
  have hsplit := smallRealValues_reorder (History.supported_small_split hs) e.small he
  have hhp := smallRealValues_product _ (smallRealValues_leftPart _ hsplit)
  have hhm := smallRealValues_product _ (smallRealValues_rightPart _ hsplit)
  change (left.root.frequency:ℝ)*(e.minus.realEval x*_) -
    (right.root.frequency:ℝ)*(e.plus.realEval x*_) = _
  dsimp only [splitSlots]
  rw [heplus,heminus,hhp,hhm]
  simp only [reversalNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast]

theorem encoded_rows_actual {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → ℝ) (Xp Xm : ℤ)
    (heplus : e.plus.realEval x = (Xp:ℝ)) (heminus : e.minus.realEval x = (Xm:ℝ))
    (he : SmallRealValues x h.root.small e.small)
    (hc : ∀ i, (comp i).realEval x = ((internalSlot h i).value:ℝ))
    (hi : (rebuild h Xp Xm).IntegralGuard) (i : InternalKey h) :
    (rows V outside h hs (encode V outside h hs e comp)
      (encode V outside h hs e comp) i).1.realEval x = (actual h Xp Xm i:ℝ) := by
  induction h generalizing Xp Xm with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
    have hu : SmallRealValues x u (fun i => comp (Sum.inl i)) := by
      intro i
      simpa only [internalSlot,Sum.elim_inl] using hc (Sum.inl i)
    have hguard := hi
    simp only [rebuild,SignedHistory.IntegralGuard,rebuild_root] at hguard
    have hpiv := pivotExpr_realEval_eq_signedPivot hs e (fun i => comp (Sum.inl i))
      x Xp Xm heplus heminus he hu hguard.1 hguard.2.1
    have hsmall := children_smallRealValues hs e (fun i => comp (Sum.inl i)) x he hu
    rcases i with i | i
    · simpa only [rows,encode,actual_node,Sum.elim_inl] using
        nodeNumerator_real_signed hs e x Xp Xm heplus heminus he
    · rcases i with i | i
      · exact ihl (History.supported_left hs) _ _ _ _ hpiv heplus hsmall.1
          (fun i => by
            simpa only [internalSlot,Sum.elim_inr,Sum.elim_inl] using hc (Sum.inr (Sum.inl i)))
          hguard.2.2.1 i
      · exact ihr (History.supported_right hs) _ _ _ _ hpiv heminus hsmall.2
          (fun i => by
            simpa only [internalSlot,Sum.elim_inr] using hc (Sum.inr (Sum.inr i)))
          hguard.2.2.2 i

end Ostmann.Arithmetic.HistorySignedNumerators

end

end OAI

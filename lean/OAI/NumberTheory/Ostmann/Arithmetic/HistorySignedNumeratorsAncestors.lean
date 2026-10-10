import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsAncestorsBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedNumerators
open Construction Characters.RationalHistory HistoryOccurrenceVariables HistorySignedDecode
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicSlots HistoryNumeratorForms
open HistoryOccurrenceRows HistorySymbolicLinearity
variable {ι : Type*}

theorem encoded_rows_actual_of_ancestorGuard {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (x : ι → ℝ) (Xp Xm : ℤ)
    (heplus : e.plus.realEval x = (Xp : ℝ)) (heminus : e.minus.realEval x = (Xm : ℝ))
    (he : SmallRealValues x h.root.small e.small)
    (hc : ∀ i, (comp i).realEval x = ((internalSlot h i).value : ℝ))
    (i : InternalKey h) (hi : AncestorIntegralGuard h Xp Xm i) :
    (rows V outside h hs (encode V outside h hs e comp)
      (encode V outside h hs e comp) i).1.realEval x = (actual h Xp Xm i : ℝ) := by
  induction h generalizing Xp Xm with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
    rcases i with i | i
    · simpa only [rows, encode, actual_node, Sum.elim_inl] using
        nodeNumerator_real_signed hs e x Xp Xm heplus heminus he
    · have hu : SmallRealValues x u (fun i => comp (Sum.inl i)) := by
        intro j
        simpa only [internalSlot, Sum.elim_inl] using hc (Sum.inl j)
      have hsmall := children_smallRealValues hs e (fun i => comp (Sum.inl i)) x he hu
      rcases i with i | i
      · have hpiv := pivotExpr_realEval_eq_signedPivot hs e (fun i => comp (Sum.inl i))
          x Xp Xm heplus heminus he hu hi.1 hi.2.1
        exact ihl (History.supported_left hs) _ _ _ _ hpiv heplus hsmall.1
          (fun j => by
            simpa only [internalSlot, Sum.elim_inr, Sum.elim_inl] using hc (Sum.inr (Sum.inl j)))
          i hi.2.2
      · have hpiv := pivotExpr_realEval_eq_signedPivot hs e (fun i => comp (Sum.inl i))
          x Xp Xm heplus heminus he hu hi.1 hi.2.1
        exact ihr (History.supported_right hs) _ _ _ _ hpiv heminus hsmall.2
          (fun j => by
            simpa only [internalSlot, Sum.elim_inr] using hc (Sum.inr (Sum.inr j)))
          i hi.2.2

theorem actual_linear_of_ancestorGuard {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (Xp Xm : ℤ)
    (i : InternalKey h) (hi : AncestorIntegralGuard h Xp Xm i) :
    (actual h Xp Xm i : ℚ) =
      (canonical h hs i).1.rationalEval (rationalSample h) * (Xp : ℚ) +
      (canonical h hs i).2.rationalEval (rationalSample h) * (Xm : ℚ) := by
  have he := encoded_rows_actual_of_ancestorGuard h hs (rootExpr h) (compensationExpr h)
    (signedGiantSample h Xp Xm) Xp Xm rfl rfl (fun _ => rfl) (fun _ => rfl) i hi
  rw [← signedRationalSample_real h Xp Xm, Expr.realEval_cast_rational] at he
  have hQ : (rows V outside h hs (symbolicHistory h hs)
      (symbolicHistory h hs) i).1.rationalEval (signedRationalSample h Xp Xm) =
      (actual h Xp Xm i : ℚ) := by
    apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_intCast, symbolicHistory] using he
  have hlin := HistoryActualNumerators.rows_linear h hs _ _ _
    (signedRationalSample h Xp Xm) _ _
    (symbolicHistory_linear h hs (signedRationalSample h Xp Xm)) i
  change _ = (canonical h hs i).1.rationalEval (signedRationalSample h Xp Xm) * (Xp : ℚ) +
    (canonical h hs i).2.rationalEval (signedRationalSample h Xp Xm) * (Xm : ℚ) at hlin
  rw [hQ] at hlin
  have hc := canonical_signedRationalSample h hs Xp Xm i
  rwa [hc.1, hc.2] at hlin

end Ostmann.Arithmetic.HistorySignedNumerators

end

end OAI

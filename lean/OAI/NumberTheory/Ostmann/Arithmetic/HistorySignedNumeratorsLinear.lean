import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedNumerators
open Construction Characters.RationalHistory HistoryOccurrenceVariables HistorySignedDecode
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicLinearity HistorySymbolicScope
open HistoryOccurrenceRows HistoryCoefficientBounds

def signedRationalSample {l : ℕ} (h : History l) (Xp Xm : ℤ) : Key h → ℚ
  | .inl false => Xp
  | .inl true => Xm
  | .inr (.inl i) => (h.root.small.get i).value
  | .inr (.inr i) => (internalSlot h i).value

theorem signedRationalSample_real {l : ℕ} (h : History l) (Xp Xm : ℤ) :
    (fun i => (signedRationalSample h Xp Xm i:ℝ))=signedGiantSample h Xp Xm := by
  funext i
  rcases i with b | i
  · cases b <;> simp only [signedRationalSample,signedGiantSample,Rat.cast_intCast]
  · rcases i with i | i <;>
      simp only [signedRationalSample,signedGiantSample,Rat.cast_natCast]

theorem rationalEval_congr_of_above {ι : Type*} {level : ι → ℕ} {t : ℕ}
    (e : Expr ι) (he : Above level t e) (x y : ι → ℚ)
    (hxy : ∀ i, t<level i → x i=y i) : e.rationalEval x=e.rationalEval y := by
  induction e with
  | atom i => exact hxy i he
  | fixed c => rfl
  | add a b ia ib | sub a b ia ib | mul a b ia ib | divide a b ia ib =>
    simp only [Expr.rationalEval,ia he.1,ib he.2]

theorem canonical_signedRationalSample {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (Xp Xm : ℤ) (i : InternalKey h) :
    (canonical h hs i).1.rationalEval (signedRationalSample h Xp Xm)=
      (canonical h hs i).1.rationalEval (rationalSample h) ∧
    (canonical h hs i).2.rationalEval (signedRationalSample h Xp Xm)=
      (canonical h hs i).2.rationalEval (rationalSample h) := by
  have hfree := rows_above h hs _ _ (rootFreeLevel h)
    (coefficientHistory_rootFreeAbove h hs false) (coefficientHistory_rootFreeAbove h hs true) i
  have hx : ∀ j, internalLevel h i<rootFreeLevel h j →
      signedRationalSample h Xp Xm j=rationalSample h j := by
    intro j hj
    rcases j with b | j
    · exact (Nat.not_lt_zero _ hj).elim
    · rcases j with j | j <;> simp only [signedRationalSample,rationalSample,integerSample,
        Int.cast_natCast]
  exact ⟨rationalEval_congr_of_above _ hfree.1 _ _ hx,
    rationalEval_congr_of_above _ hfree.2 _ _ hx⟩

theorem actual_linear {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) (i : InternalKey h) :
    (actual h Xp Xm i:ℚ) =
      (canonical h hs i).1.rationalEval (rationalSample h)*(Xp:ℚ)+
        (canonical h hs i).2.rationalEval (rationalSample h)*(Xm:ℚ) := by
  have he := encoded_rows_actual h hs (rootExpr h) (compensationExpr h)
    (signedGiantSample h Xp Xm) Xp Xm rfl rfl (fun _ => rfl) (fun _ => rfl) hi i
  rw [← signedRationalSample_real h Xp Xm,Expr.realEval_cast_rational] at he
  have hQ : (rows V outside h hs (symbolicHistory h hs)
      (symbolicHistory h hs) i).1.rationalEval (signedRationalSample h Xp Xm)=
      (actual h Xp Xm i:ℚ) := by
    apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_intCast,symbolicHistory] using he
  have hlin := HistoryActualNumerators.rows_linear h hs _ _ _
    (signedRationalSample h Xp Xm) _ _
    (symbolicHistory_linear h hs (signedRationalSample h Xp Xm)) i
  change _ = (canonical h hs i).1.rationalEval (signedRationalSample h Xp Xm)*(Xp:ℚ)+
    (canonical h hs i).2.rationalEval (signedRationalSample h Xp Xm)*(Xm:ℚ) at hlin
  rw [hQ] at hlin
  have hc := canonical_signedRationalSample h hs Xp Xm i
  rwa [hc.1,hc.2] at hlin

end Ostmann.Arithmetic.HistorySignedNumerators

end

end OAI

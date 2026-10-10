import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsAncestors
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsPair

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedNumerators
open Construction Characters.RationalHistory HistoryOccurrenceVariables HistorySignedDecode
open HistoryPairPattern HistoryPairRows HistoryOccurrenceRows ClearedCoefficientFlags MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def PairAncestorIntegralGuard (h k : History l) (Xp Xm : ℤ) : Occurrences h k → Prop :=
  Sum.elim (AncestorIntegralGuard h Xp Xm) (AncestorIntegralGuard k Xp Xm)

theorem pairActual_linear_of_ancestorGuard (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (Xp Xm : ℤ)
    (i : Occurrences h k) (hi : PairAncestorIntegralGuard h k Xp Xm i) :
    (pairActual h k Xp Xm i : ℚ) =
      (row h k hs ks i).1.rationalEval (pairRationalSample h k) * (Xp : ℚ) +
      (row h k hs ks i).2.rationalEval (pairRationalSample h k) * (Xm : ℚ) := by
  rcases i with i | i
  · simpa only [pairActual, Sum.elim_inl, row, left_rationalEval] using
      actual_linear_of_ancestorGuard h hs Xp Xm i hi
  · simpa only [pairActual, Sum.elim_inr, row, right_rationalEval h k hroot] using
      actual_linear_of_ancestorGuard k ks Xp Xm i hi

theorem pairActual_integer_linear_cleared_of_ancestorGuard (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (Xp Xm : ℤ)
    (i : Occurrences h k) (hi : PairAncestorIntegralGuard h k Xp Xm i) :
    eval (pairSample h k) (commonDenominator (row h k hs ks i).1 (row h k hs ks i).2) *
      pairActual h k Xp Xm i =
      eval (pairSample h k) (leftFlag h k hs ks i) * Xp +
      eval (pairSample h k) (rightFlag h k hs ks i) * Xm := by
  obtain ⟨ha, hb, _⟩ := row_regular_nonzero h k hs ks hroot i
  have hc := coefficients_cleared (row h k hs ks i).1 (row h k hs ks i).2
    (pairRationalSample h k) ((Expr.fieldRegularAt_rat _ _).mpr ha)
      ((Expr.fieldRegularAt_rat _ _).mpr hb)
  simp only [Expr.fieldEval_rat] at hc
  have hQ : eval₂ (Int.castRingHom ℚ) (pairRationalSample h k)
      (commonDenominator (row h k hs ks i).1 (row h k hs ks i).2) *
        (pairActual h k Xp Xm i : ℚ) =
      eval₂ (Int.castRingHom ℚ) (pairRationalSample h k) (leftFlag h k hs ks i) * (Xp : ℚ) +
      eval₂ (Int.castRingHom ℚ) (pairRationalSample h k) (rightFlag h k hs ks i) * (Xm : ℚ) := by
    rw [pairActual_linear_of_ancestorGuard h k hs ks hroot Xp Xm i hi]
    change _ = eval₂ _ _ (leftCoefficient _ _) * _ + eval₂ _ _ (rightCoefficient _ _) * _
    rw [hc.2.1, hc.2.2]
    ring
  have he : ∀ P : MvPolynomial (PairKey h k) ℤ,
      eval₂ (Int.castRingHom ℚ) (pairRationalSample h k) P =
        (eval (pairSample h k) P : ℚ) := fun P => Expr.eval₂_cast_int P (pairSample h k)
  rw [he, he, he] at hQ
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul, Int.cast_add] using hQ

theorem pairActual_power_dvd_iff_of_ancestorGuard (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (Xp Xm : ℤ)
    (i : Occurrences h k) (hi : PairAncestorIntegralGuard h k Xp Xm i) (p n : ℕ) [Fact p.Prime]
    (hx : AncestorUnits h k (fun j => (pairSample h k j : ZMod p)) i)
    (hV : ∀ j ≤ l, V j < p) :
    (p : ℤ)^n ∣ pairActual h k Xp Xm i ↔
      (p : ℤ)^n ∣ eval (pairSample h k) (leftFlag h k hs ks i) * Xp +
        eval (pairSample h k) (rightFlag h k hs ks i) * Xm := by
  obtain ⟨ha, hb, _⟩ := row_regular_nonzero_field h k hs ks i _ hx
    (HistoryPairNumerators.frequency_units h k hs ks p hV)
  have hd := (coefficients_cleared (row h k hs ks i).1 (row h k hs ks i).2 _ ha hb).1
  rw [Expr.eval₂_cast_int] at hd
  exact HistoryPrimeSquareSupport.power_dvd_cleared_iff p n _ _ _ _ _ _ hd
    (pairActual_integer_linear_cleared_of_ancestorGuard h k hs ks hroot Xp Xm i hi)

end Ostmann.Arithmetic.HistorySignedNumerators

end

end OAI

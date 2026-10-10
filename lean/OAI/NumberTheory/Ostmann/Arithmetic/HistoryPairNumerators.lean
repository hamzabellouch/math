import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRows
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrimeSquareSupport

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairNumerators
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryOccurrenceRows ClearedCoefficientFlags MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def actual (h k : History l) : Occurrences h k → ℤ :=
  Sum.elim (HistoryActualNumerators.actual h) (HistoryActualNumerators.actual k)

theorem actual_divisible (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) : ((slot h k i).value:ℤ) ∣ actual h k i := by
  rcases i with i | i
  · exact HistoryActualNumerators.actual_divisible h hs i
  · exact HistoryActualNumerators.actual_divisible k ks i

theorem actual_linear (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (i : Occurrences h k) :
    (actual h k i:ℚ) =
      (row h k hs ks i).1.rationalEval (pairRationalSample h k)*(h.root.giantPlus:ℚ)+
      (row h k hs ks i).2.rationalEval (pairRationalSample h k)*(h.root.giantMinus:ℚ) := by
  rcases i with i | i
  · simpa only [actual,Sum.elim_inl,row,left_rationalEval] using
      HistoryActualNumerators.actual_linear h hs i
  · simpa only [actual,Sum.elim_inr,row,right_rationalEval h k hroot,hroot.1,hroot.2] using
      HistoryActualNumerators.actual_linear k ks i

theorem integer_linear_cleared (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (i : Occurrences h k) :
    eval (pairSample h k) (commonDenominator (row h k hs ks i).1 (row h k hs ks i).2)*
      actual h k i =
    eval (pairSample h k) (leftFlag h k hs ks i)*(h.root.giantPlus:ℤ)+
    eval (pairSample h k) (rightFlag h k hs ks i)*(h.root.giantMinus:ℤ) := by
  obtain ⟨ha,hb,_⟩ := row_regular_nonzero h k hs ks hroot i
  have hc := coefficients_cleared (row h k hs ks i).1 (row h k hs ks i).2
    (pairRationalSample h k) ((Expr.fieldRegularAt_rat _ _).mpr ha)
      ((Expr.fieldRegularAt_rat _ _).mpr hb)
  simp only [Expr.fieldEval_rat] at hc
  have hQ : eval₂ (Int.castRingHom ℚ) (pairRationalSample h k)
      (commonDenominator (row h k hs ks i).1 (row h k hs ks i).2)*(actual h k i:ℚ) =
      eval₂ (Int.castRingHom ℚ) (pairRationalSample h k) (leftFlag h k hs ks i)*(h.root.giantPlus:ℚ)+
      eval₂ (Int.castRingHom ℚ) (pairRationalSample h k) (rightFlag h k hs ks i)*(h.root.giantMinus:ℚ) := by
    rw [actual_linear h k hs ks hroot i]
    change _ = eval₂ _ _ (leftCoefficient _ _)*_+eval₂ _ _ (rightCoefficient _ _)*_
    rw [hc.2.1,hc.2.2]
    ring
  have he : ∀ P : MvPolynomial (PairKey h k) ℤ,
      eval₂ (Int.castRingHom ℚ) (pairRationalSample h k) P =
        (eval (pairSample h k) P:ℚ) := fun P => Expr.eval₂_cast_int P (pairSample h k)
  rw [he,he,he] at hQ
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using hQ

theorem actual_line_zero (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (i : Occurrences h k) :
    let p := (slot h k i).value
    eval₂ (Int.castRingHom (ZMod p)) (fun j => (pairSample h k j:ZMod p))
      (leftFlag h k hs ks i)*(h.root.giantPlus:ZMod p)+
    eval₂ (Int.castRingHom (ZMod p)) (fun j => (pairSample h k j:ZMod p))
      (rightFlag h k hs ks i)*(h.root.giantMinus:ZMod p)=0 := by
  dsimp only
  rw [Expr.eval₂_cast_int,Expr.eval₂_cast_int]
  have he := congrArg (fun z : ℤ => (z:ZMod (slot h k i).value))
    (integer_linear_cleared h k hs ks hroot i)
  have hz : (actual h k i:ZMod (slot h k i).value)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (actual_divisible h k hs ks i)
  simp only [Int.cast_mul,Int.cast_add,Int.cast_natCast,hz,mul_zero] at he
  exact he.symm

theorem frequency_units (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (p : ℕ) (hV : ∀ j ≤ l, V j < p) :
    ∀ s ∈ h.frequencies ++ k.frequencies, (s:ZMod p)≠0 := by
  intro s hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact HistoryPrimeRows.frequency_units h hs p hV s hmem
  · exact HistoryPrimeRows.frequency_units k ks p hV s hmem

theorem actual_power_dvd_iff (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (i : Occurrences h k) (p n : ℕ) [Fact p.Prime]
    (hx : AncestorUnits h k (fun j => (pairSample h k j:ZMod p)) i)
    (hV : ∀ j ≤ l, V j < p) :
    (p:ℤ)^n ∣ actual h k i ↔
      (p:ℤ)^n ∣ eval (pairSample h k) (leftFlag h k hs ks i)*(h.root.giantPlus:ℤ)+
        eval (pairSample h k) (rightFlag h k hs ks i)*(h.root.giantMinus:ℤ) := by
  obtain ⟨ha,hb,_⟩ := row_regular_nonzero_field h k hs ks i _ hx (frequency_units h k hs ks p hV)
  have hd := (coefficients_cleared (row h k hs ks i).1 (row h k hs ks i).2 _ ha hb).1
  rw [Expr.eval₂_cast_int] at hd
  exact HistoryPrimeSquareSupport.power_dvd_cleared_iff p n _ _ _ _ _ _ hd
    (integer_linear_cleared h k hs ks hroot i)

end Ostmann.Arithmetic.HistoryPairNumerators

end

end OAI

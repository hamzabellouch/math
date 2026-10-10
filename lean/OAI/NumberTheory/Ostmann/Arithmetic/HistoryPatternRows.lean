import OAI.NumberTheory.Ostmann.Arithmetic.ClearedCoefficientFlags
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryOccurrenceRows
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepeatedRenamingPattern

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPatternRows
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicScope HistoryOccurrenceRows HistoryRepeatedRenaming ClearedCoefficientFlags
open MvPolynomial

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def row (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    Expr (PatternKey h) × Expr (PatternKey h) :=
  ((canonical h hs i).1.rename (patternMap h),(canonical h hs i).2.rename (patternMap h))

def leftFlag (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    MvPolynomial (PatternKey h) ℤ := leftCoefficient (row h hs i).1 (row h hs i).2

def rightFlag (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    MvPolynomial (PatternKey h) ℤ := rightCoefficient (row h hs i).1 (row h hs i).2

def minorFlag (h : History l) (hs : h.Supported V outside) (i j : InternalKey h) :
    MvPolynomial (PatternKey h) ℤ :=
  minor (row h hs i).1 (row h hs i).2 (row h hs j).1 (row h hs j).2

def sample (h : History l) : PatternKey h → ℚ := fun j => (patternSample h j.val : ℚ)

theorem sample_comp (h : History l) : sample h ∘ patternMap h = rationalSample h := by
  funext i
  exact congrArg (fun z : ℤ => (z:ℚ)) (patternMap_sample h i)

theorem row_regular_nonzero (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    (row h hs i).1.RegularAt (sample h) ∧ (row h hs i).2.RegularAt (sample h) ∧
      ((row h hs i).1.rationalEval (sample h) ≠ 0 ∨
        (row h hs i).2.rationalEval (sample h) ≠ 0) := by
  simpa only [row,Expr.regularAt_rename,Expr.rationalEval_rename,sample_comp] using
    canonical_regular_nonzero h hs i

theorem flags_eval_nonzero (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    eval₂ (Int.castRingHom ℚ) (sample h) (leftFlag h hs i) ≠ 0 ∨
      eval₂ (Int.castRingHom ℚ) (sample h) (rightFlag h hs i) ≠ 0 := by
  obtain ⟨ha,hb,hab⟩ := row_regular_nonzero h hs i
  obtain ⟨ha0,hea⟩ := (row h hs i).1.rational_cleared (sample h) ha
  obtain ⟨hb0,heb⟩ := (row h hs i).2.rational_cleared (sample h) hb
  rcases hab with ha | hb
  · left
    change eval₂ _ _ ((row h hs i).1.numerator*(row h hs i).2.denominator) ≠ 0
    rw [eval₂_mul,← hea]
    exact mul_ne_zero (mul_ne_zero ha0 ha) hb0
  · right
    change eval₂ _ _ ((row h hs i).2.numerator*(row h hs i).1.denominator) ≠ 0
    rw [eval₂_mul,← heb]
    exact mul_ne_zero (mul_ne_zero hb0 hb) ha0

theorem flags_nonzero (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    leftFlag h hs i ≠ 0 ∨ rightFlag h hs i ≠ 0 := by
  rcases flags_eval_nonzero h hs i with h | h
  · exact Or.inl (fun hz => h (by rw [hz]; exact eval₂_zero _ _))
  · exact Or.inr (fun hz => h (by rw [hz]; exact eval₂_zero _ _))

theorem row_above (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    Above (fun j : PatternKey h => patternLevel l j.val) (internalLevel h i) (row h hs i).1 ∧
      Above (fun j : PatternKey h => patternLevel l j.val) (internalLevel h i) (row h hs i).2 := by
  have hi := canonical_above h hs i
  exact ⟨(above_rename _ (patternMap h) (keyLevel h)
      (fun j : PatternKey h => patternLevel l j.val) (patternMap_level h) _).mpr hi.1,
    (above_rename _ (patternMap h) (keyLevel h)
      (fun j : PatternKey h => patternLevel l j.val) (patternMap_level h) _).mpr hi.2⟩

theorem flags_above (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    PolynomialAbove (fun j : PatternKey h => patternLevel l j.val) (internalLevel h i)
      (leftFlag h hs i) ∧
    PolynomialAbove (fun j : PatternKey h => patternLevel l j.val) (internalLevel h i)
      (rightFlag h hs i) := by
  have hi := row_above h hs i
  have he := coefficients_above _ _ _ _ hi.1 hi.2
  exact ⟨he.1,he.2.1⟩

theorem minorFlag_above (h : History l) (hs : h.Supported V outside) (i j : InternalKey h)
    (hlevel : internalLevel h i = internalLevel h j) :
    PolynomialAbove (fun j : PatternKey h => patternLevel l j.val) (internalLevel h i)
      (minorFlag h hs i j) := by
  have hi := row_above h hs i
  have hj := row_above h hs j
  rw [← hlevel] at hj
  exact minor_above _ _ _ _ _ _ hi.1 hi.2 hj.1 hj.2

theorem flag_degrees (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    (leftFlag h hs i).totalDegree ≤ 2*(2^l*(h.root.small.length+2*h.internalOccurrences.length)) ∧
    (rightFlag h hs i).totalDegree ≤ 2*(2^l*(h.root.small.length+2*h.internalOccurrences.length)) := by
  have hc := canonical_atomCount h hs i
  have hd := coefficient_degrees (row h hs i).1 (row h hs i).2
  simp only [row,Expr.atomCount_rename] at hd
  exact ⟨hd.1.trans (by omega),hd.2.1.trans (by omega)⟩

theorem minorFlag_degree (h : History l) (hs : h.Supported V outside) (i j : InternalKey h) :
    (minorFlag h hs i j).totalDegree ≤
      4*(2^l*(h.root.small.length+2*h.internalOccurrences.length)) := by
  have hi := canonical_atomCount h hs i
  have hj := canonical_atomCount h hs j
  have hd := minor_degree (row h hs i).1 (row h hs i).2 (row h hs j).1 (row h hs j).2
  simp only [row,Expr.atomCount_rename] at hd
  exact hd.trans (by omega)

end Ostmann.Arithmetic.HistoryPatternRows

end

end OAI

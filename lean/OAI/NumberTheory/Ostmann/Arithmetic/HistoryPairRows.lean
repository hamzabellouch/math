import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActualNumerators
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairPattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrimeRows

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairRows
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryOccurrenceRows HistoryPairPattern ClearedCoefficientFlags HistorySymbolicScope
open MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

abbrev Occurrences (h k : History l) := InternalKey h ⊕ InternalKey k

def level (h k : History l) : Occurrences h k → ℕ :=
  Sum.elim (internalLevel h) (internalLevel k)

def slot (h k : History l) : Occurrences h k → SmallSlot :=
  Sum.elim (internalSlot h) (internalSlot k)

def row (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside) :
    Occurrences h k → Expr (PairKey h k) × Expr (PairKey h k) :=
  Sum.elim
    (fun i => ((canonical h hs i).1.rename (leftMap h k),
      (canonical h hs i).2.rename (leftMap h k)))
    (fun i => ((canonical k ks i).1.rename (rightMap h k),
      (canonical k ks i).2.rename (rightMap h k)))

def leftFlag (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) : MvPolynomial (PairKey h k) ℤ :=
  leftCoefficient (row h k hs ks i).1 (row h k hs ks i).2

def rightFlag (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) : MvPolynomial (PairKey h k) ℤ :=
  rightCoefficient (row h k hs ks i).1 (row h k hs ks i).2

def minorFlag (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i j : Occurrences h k) : MvPolynomial (PairKey h k) ℤ :=
  minor (row h k hs ks i).1 (row h k hs ks i).2
    (row h k hs ks j).1 (row h k hs ks j).2

theorem row_above (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) :
    Above (pairLevel h k) (level h k i) (row h k hs ks i).1 ∧
    Above (pairLevel h k) (level h k i) (row h k hs ks i).2 := by
  rcases i with i | i
  · exact ⟨(left_above _ _ _ _).mpr (canonical_above h hs i).1,
      (left_above _ _ _ _).mpr (canonical_above h hs i).2⟩
  · exact ⟨(right_above _ _ _ _).mpr (canonical_above k ks i).1,
      (right_above _ _ _ _).mpr (canonical_above k ks i).2⟩

theorem flags_above (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) :
    PolynomialAbove (pairLevel h k) (level h k i) (leftFlag h k hs ks i) ∧
    PolynomialAbove (pairLevel h k) (level h k i) (rightFlag h k hs ks i) := by
  have hi := row_above h k hs ks i
  have hc := coefficients_above _ _ _ _ hi.1 hi.2
  exact ⟨hc.1,hc.2.1⟩

theorem minorFlag_above (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i j : Occurrences h k) (hlevel : level h k i=level h k j) :
    PolynomialAbove (pairLevel h k) (level h k i) (minorFlag h k hs ks i j) := by
  have hi := row_above h k hs ks i
  have hj := row_above h k hs ks j
  rw [← hlevel] at hj
  exact minor_above _ _ _ _ _ _ hi.1 hi.2 hj.1 hj.2

theorem row_regular_nonzero (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (i : Occurrences h k) :
    (row h k hs ks i).1.RegularAt (pairRationalSample h k) ∧
    (row h k hs ks i).2.RegularAt (pairRationalSample h k) ∧
      ((row h k hs ks i).1.rationalEval (pairRationalSample h k)≠0 ∨
       (row h k hs ks i).2.rationalEval (pairRationalSample h k)≠0) := by
  rcases i with i | i
  · simpa only [row,Sum.elim_inl,left_regularAt,left_rationalEval] using
      canonical_regular_nonzero h hs i
  · simpa only [row,Sum.elim_inr,right_regularAt h k hroot,right_rationalEval h k hroot] using
      canonical_regular_nonzero k ks i

def AncestorUnits {K : Type*} [Zero K] (h k : History l)
    (x : PairKey h k → K) : Occurrences h k → Prop :=
  Sum.elim
    (fun i => ∀ j : Fin h.root.small.length ⊕ InternalKey h,
      internalLevel h i < keyLevel h (.inr j) → x (leftMap h k (.inr j)) ≠ 0)
    (fun i => ∀ j : Fin k.root.small.length ⊕ InternalKey k,
      internalLevel k i < keyLevel k (.inr j) → x (rightMap h k (.inr j)) ≠ 0)

theorem row_regular_nonzero_field {K : Type*} [Field K]
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) (x : PairKey h k → K) (hx : AncestorUnits h k x i)
    (hf : ∀ s ∈ h.frequencies ++ k.frequencies, (s:K)≠0) :
    (row h k hs ks i).1.FieldRegularAt x ∧ (row h k hs ks i).2.FieldRegularAt x ∧
      ((row h k hs ks i).1.fieldEval x≠0 ∨ (row h k hs ks i).2.fieldEval x≠0) := by
  rcases i with i | i
  · have hf' := fun s hs => hf s (List.mem_append_left _ hs)
    have hr := HistoryFieldIndependence.canonical_regular h hs i (x ∘ leftMap h k) hx hf'
    have hn := HistoryFieldIndependence.canonical_nonzero h hs i (x ∘ leftMap h k) hx hf'
    simpa only [row,Sum.elim_inl,Expr.fieldRegularAt_rename,Expr.fieldEval_rename] using
      And.intro hr.1 (And.intro hr.2 hn)
  · have hf' := fun s hs => hf s (List.mem_append_right _ hs)
    have hr := HistoryFieldIndependence.canonical_regular k ks i (x ∘ rightMap h k) hx hf'
    have hn := HistoryFieldIndependence.canonical_nonzero k ks i (x ∘ rightMap h k) hx hf'
    simpa only [row,Sum.elim_inr,Expr.fieldRegularAt_rename,Expr.fieldEval_rename] using
      And.intro hr.1 (And.intro hr.2 hn)

theorem flags_nonzero_field {K : Type*} [Field K]
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) (x : PairKey h k → K) (hx : AncestorUnits h k x i)
    (hf : ∀ s ∈ h.frequencies ++ k.frequencies, (s:K)≠0) :
    eval₂ (Int.castRingHom K) x (leftFlag h k hs ks i)≠0 ∨
    eval₂ (Int.castRingHom K) x (rightFlag h k hs ks i)≠0 := by
  obtain ⟨ha,hb,hn⟩ := row_regular_nonzero_field h k hs ks i x hx hf
  exact (row_nonzero_iff _ _ x ha hb).mpr hn

def degreeBudget (h k : History l) : ℕ :=
  2^l*(h.root.small.length+2*h.internalOccurrences.length)+
  2^l*(k.root.small.length+2*k.internalOccurrences.length)

theorem row_atomCount (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) :
    (row h k hs ks i).1.atomCount ≤ degreeBudget h k ∧
    (row h k hs ks i).2.atomCount ≤ degreeBudget h k := by
  rcases i with i | i
  · have hh := canonical_atomCount h hs i
    simp only [row,Sum.elim_inl,Expr.atomCount_rename,degreeBudget]
    omega
  · have hh := canonical_atomCount k ks i
    simp only [row,Sum.elim_inr,Expr.atomCount_rename,degreeBudget]
    omega

theorem flag_degrees (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) :
    (leftFlag h k hs ks i).totalDegree ≤ 2*degreeBudget h k ∧
    (rightFlag h k hs ks i).totalDegree ≤ 2*degreeBudget h k := by
  have hr := row_atomCount h k hs ks i
  have hc := coefficient_degrees (row h k hs ks i).1 (row h k hs ks i).2
  exact ⟨hc.1.trans (by omega),hc.2.1.trans (by omega)⟩

theorem minorFlag_degree (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i j : Occurrences h k) :
    (minorFlag h k hs ks i j).totalDegree ≤ 4*degreeBudget h k := by
  have hi := row_atomCount h k hs ks i
  have hj := row_atomCount h k hs ks j
  exact (minor_degree (row h k hs ks i).1 (row h k hs ks i).2
    (row h k hs ks j).1 (row h k hs ks j).2).trans (by omega)

end Ostmann.Arithmetic.HistoryPairRows

end

end OAI

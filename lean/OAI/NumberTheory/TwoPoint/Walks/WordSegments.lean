import OAI.NumberTheory.TwoPoint.Walks.BlockGeometry

namespace OAI

/-! Exact identification of list segments with integer displacement intervals. -/

namespace TwoPointCorrelations

open Finset

def wordStepDisplacement (h : ℕ) (w : List SignedStep) (i : ℕ) : ℤ :=
  ((w[i]?).map (SignedStep.displacement h)).getD 0

@[simp] lemma wordStepDisplacement_nil (h i : ℕ) : wordStepDisplacement h [] i = 0 := by
  simp [wordStepDisplacement]

@[simp] lemma wordStepDisplacement_cons_zero (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) 0 = a.displacement h := rfl

@[simp] lemma wordStepDisplacement_cons_succ (h i : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) (i + 1) = wordStepDisplacement h w i := rfl

lemma wordDisplacement_take (h : ℕ) (w : List SignedStep) (n : ℕ) :
    wordDisplacement h (w.take n) = ∑ i ∈ range n, wordStepDisplacement h w i := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      cases w with
      | nil => simp
      | cons a w =>
          rw [List.take_succ_cons, wordDisplacement_cons, Finset.sum_range_succ']
          simp only [wordStepDisplacement_cons_zero, wordStepDisplacement_cons_succ, ih]
          ring

def wordSlice (w : List SignedStep) (a b : ℕ) : List SignedStep := (w.drop a).take (b - a)

lemma wordSlice_length (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ w.length) :
    (wordSlice w a b).length = b - a := by
  simp only [wordSlice, List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

lemma wordSlice_split (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) :
    w.take a ++ wordSlice w a b = w.take b := by
  have h := List.take_append_drop a (w.take b)
  simpa only [List.take_take, Nat.min_eq_left hab, List.drop_take, wordSlice] using h

lemma wordSlice_infix (w : List SignedStep) (a b : ℕ) : wordSlice w a b <:+: w := by
  refine ⟨w.take a, (w.drop a).drop (b - a), ?_⟩
  change (w.take a ++ (w.drop a).take (b - a)) ++ (w.drop a).drop (b - a) = w
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

lemma wordSlice_displacement (h : ℕ) (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) :
    wordDisplacement h (wordSlice w a b) = intervalDisplacement (wordStepDisplacement h w) a b := by
  have hs := congrArg (wordDisplacement h) (wordSlice_split w hab)
  rw [wordDisplacement_append, wordDisplacement_take, wordDisplacement_take] at hs
  rw [intervalDisplacement_eq_sub _ hab]
  omega

lemma wordSlice_drop (w : List SignedStep) {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b) :
    (wordSlice w a b).drop (c - a) = wordSlice w c b := by
  simp only [wordSlice, List.drop_take, List.drop_drop]
  rw [show b - a - (c - a) = b - c by omega,
    show a + (c - a) = c by omega]

lemma tuplePrimeAt_slice (w : List SignedStep) (a b p i : ℕ) (hi : i < b - a) :
    TuplePrimeAt (wordSlice w a b) p i ↔ TuplePrimeAt w p (a + i) := by
  unfold TuplePrimeAt wordSlice
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop]

lemma TuplePrimeAt.index_lt {w : List SignedStep} {p i : ℕ} (hp : TuplePrimeAt w p i) :
    i < w.length := by
  obtain ⟨_, a, ha, _⟩ := hp
  exact (List.getElem?_eq_some_iff.mp ha).1

/-- The purely local interval prohibition is exactly a forward-prohibited
list segment when eligibility and unequal consecutive tuples are retained. -/
lemma prohibitedInterval_forward_wordSlice (h s : ℕ) (supply : ℕ → ℕ → Prop)
    (w : List SignedStep) (hlen : w.length ≤ s)
    (hsupply : ∀ t ∈ w, supply t.tuple t.padding)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple)) {a b : ℕ}
    (hb : b ≤ w.length)
    (hpro : ProhibitedInterval (TuplePrimeAt w) (wordStepDisplacement h w) id a b) :
    ForwardProhibited h s supply (wordSlice w a b) := by
  rcases hpro with ⟨hlenab, hinterval, p, hfirst, hlast, c, hac, hcb, hdiv⟩
  have hab : a ≤ b := by omega
  have hlength := wordSlice_length w hab hb
  refine ⟨by omega, by omega, ?_, (hchain.drop a).take (b - a), ?_, p, ?_, ?_,
    c - a, by omega, by omega, ?_⟩
  · intro t ht
    exact hsupply t ((wordSlice_infix w a b).subset ht)
  · intro q i j k hij hjk hk hqi hqk
    have hi : i < b - a := by omega
    have hj : j < b - a := by omega
    have hk' : k < b - a := by omega
    apply (tuplePrimeAt_slice w a b q j hj).mpr
    apply hinterval q (a + i) (a + j) (a + k) (by omega) (by omega) (by omega) (by omega)
    · exact (tuplePrimeAt_slice w a b q i hi).mp hqi
    · exact (tuplePrimeAt_slice w a b q k hk').mp hqk
  · simpa only [Nat.add_zero] using (tuplePrimeAt_slice w a b p 0 (by omega)).mpr hfirst
  · intro hp
    have hp' := (tuplePrimeAt_slice w a b p ((wordSlice w a b).length - 1) (by omega)).mp hp
    have heq : a + ((wordSlice w a b).length - 1) = b - 1 := by omega
    exact hlast (heq ▸ hp')
  · rw [wordSlice_drop w hac.le (by omega), wordSlice_displacement h w (by omega)]
    exact hdiv

/-- The local prohibition hypothesis used by block geometry is discharged
from survival of the actual main vertices, via concrete witness descent. -/
theorem PositiveWord.avoids_prohibitedIntervals {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {x : ℤ} {w : List SignedStep} (hw : PositiveWord h x w)
    (hsurvive : ∀ y, WordVertex h x w y → ¬ProhibitedSite h s supply y)
    (hlen : w.length ≤ s) (hsupply : ∀ t ∈ w, supply t.tuple t.padding)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple)) :
    ∀ a b, b ≤ w.length → ¬ProhibitedInterval (TuplePrimeAt w) (wordStepDisplacement h w) id a b := by
  intro a b hb hpro
  have hword := prohibitedInterval_forward_wordSlice h s supply w hlen hsupply hchain hb hpro
  exact hw.not_prohibited_orientedInfix hsurvive (Or.inl (wordSlice_infix w a b)) hword

end TwoPointCorrelations

end OAI

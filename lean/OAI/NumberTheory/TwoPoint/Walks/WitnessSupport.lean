import OAI.NumberTheory.TwoPoint.Walks.WitnessCover
import OAI.NumberTheory.TwoPoint.Walks.WordBlockGeometry

namespace OAI

/-! Concrete prime supports of numerical witness words. -/

namespace TwoPointCorrelations

open Finset

/-- The distinct prime factors of the whole tuples in a word. -/
def wordPrimeSupport : List SignedStep → Finset ℕ
  | [] => ∅
  | a :: w => a.tuple.primeFactors ∪ wordPrimeSupport w

lemma mem_wordPrimeSupport (p : ℕ) (w : List SignedStep) :
    p ∈ wordPrimeSupport w ↔ ∃ a ∈ w, p ∈ a.tuple.primeFactors := by
  induction w with
  | nil => simp [wordPrimeSupport]
  | cons a w ih => simp only [wordPrimeSupport, mem_union, ih, List.mem_cons]; aesop

lemma mem_wordPrimeSupport_iff (p : ℕ) (w : List SignedStep)
    (hsq : ∀ a ∈ w, Squarefree a.tuple) :
    p ∈ wordPrimeSupport w ↔ ∃ i, TuplePrimeAt w p i := by
  rw [mem_wordPrimeSupport]
  constructor
  · rintro ⟨a, ha, hp⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    have hprime := Nat.mem_primeFactors.mp hp
    exact ⟨i, hprime.1, a, hi, hprime.2.1⟩
  · rintro ⟨i, hp, a, hi, hpa⟩
    have ha : a ∈ w := List.mem_iff_getElem?.mpr ⟨i, hi⟩
    exact ⟨a, ha, Nat.mem_primeFactors.mpr ⟨hp, hpa, (hsq a ha).ne_zero⟩⟩

lemma wordPrimeSupport_card_le (w : List SignedStep) (J : ℕ)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card ≤ J) :
    (wordPrimeSupport w).card ≤ w.length * J := by
  induction w with
  | nil => simp [wordPrimeSupport]
  | cons a w ih =>
      have hw := ih (fun b hb => hcard b (List.mem_cons_of_mem a hb))
      have ha := hcard a (List.mem_cons_self)
      calc
        (wordPrimeSupport (a :: w)).card ≤ a.tuple.primeFactors.card + (wordPrimeSupport w).card :=
          Finset.card_union_le _ _
        _ ≤ J + w.length * J := Nat.add_le_add ha hw
        _ = (a :: w).length * J := by simp [Nat.add_mul, Nat.add_comm]

/-- Support restricted to the injectively numbered singleton coordinates. -/
def wordCoordinateSupport {ι : Type*} [Fintype ι] (prime : ι → ℕ) (w : List SignedStep) : Finset ι :=
  Finset.univ.filter (fun i => prime i ∈ wordPrimeSupport w)

lemma wordCoordinateSupport_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime : ι → ℕ) (hinj : Function.Injective prime) (w : List SignedStep) (J : ℕ)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card ≤ J) :
    (wordCoordinateSupport prime w).card ≤ w.length * J := by
  apply (Finset.card_le_card_of_injOn prime ?_ (fun _ _ _ _ heq => hinj heq)).trans
    (wordPrimeSupport_card_le w J hcard)
  intro i hi
  exact (Finset.mem_filter.mp hi).2

/-- Numerical witness words of length at most `s` have at most `s*J`
singleton coordinates in their support. -/
lemma bounded_wordCoordinateSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime : ι → ℕ) (hinj : Function.Injective prime) (w : List SignedStep) (s J : ℕ)
    (hlen : w.length ≤ s) (hcard : ∀ a ∈ w, a.tuple.primeFactors.card ≤ J) :
    (wordCoordinateSupport prime w).card ≤ s * J :=
  (wordCoordinateSupport_card_le prime hinj w J hcard).trans (Nat.mul_le_mul_right J hlen)

/-- The witness-cover conclusion with actual numerical words and actual
prime occurrences. Every selected word is positive in the same hybrid,
and its marked prime occurs in no other selected word. -/
theorem numerical_witness_cover {ι W A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (prime : ι → ℕ) (hinj : Function.Injective prime)
    (word : W → List SignedStep) (I : W → (ι → A) → Bool) (a x : ι → A)
    (hdepends : ∀ w, DependsOn (wordCoordinateSupport prime (word w)) (I w))
    (hnonzero : mixedDifference a (witnessAvoidance I) x ≠ 0)
    (s J T : ℕ) (hlen : ∀ w, (word w).length ≤ s)
    (hsq : ∀ w t, t ∈ word w → Squarefree t.tuple)
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card ≤ J)
    (hT : T * (s * J) < Fintype.card ι) :
    ∃ R : Finset W, R.card = T ∧ ∃ H : Finset ι,
      (∀ w ∈ R, I w (forceCoordinates H a x) = true) ∧
      ∃ mark : R → ι, Function.Injective mark ∧
        ∀ w : R, (∃ i, TuplePrimeAt (word w) (prime (mark w)) i) ∧
          ∀ v ∈ R, v ≠ w → ¬∃ i, TuplePrimeAt (word v) (prime (mark w)) i := by
  obtain ⟨R, hR, H, hI, mark, hinjmark, hmark⟩ :=
    mixedDifference_private_witnesses (fun w => wordCoordinateSupport prime (word w))
      I hdepends a x hnonzero (s * J) T
      (fun w => bounded_wordCoordinateSupport prime hinj (word w) s J (hlen w) (hcard w)) hT
  refine ⟨R, hR, H, hI, mark, hinjmark, ?_⟩
  intro w
  constructor
  · apply (mem_wordPrimeSupport_iff _ _ (hsq w)).mp
    exact (Finset.mem_filter.mp (hmark w).1).2
  · intro v hv hne hocc
    apply (hmark w).2 v hv hne
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (mem_wordPrimeSupport_iff _ _ (hsq v)).mpr hocc⟩

end TwoPointCorrelations

end OAI

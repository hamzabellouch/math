import OAI.NumberTheory.TwoPoint.Walks.WordSegments
import Mathlib.Data.Nat.Squarefree

namespace OAI

/-! Geometry of actual surviving positive words, including the prime-support checks. -/

namespace TwoPointCorrelations

open Finset

lemma tuplePrimeAt_iff_getElem (w : List SignedStep) (p i : ℕ) (hi : i < w.length) :
    TuplePrimeAt w p i ↔ p.Prime ∧ p ∣ w[i].tuple := by
  simp [TuplePrimeAt, List.getElem?_eq_getElem hi]

lemma wordStepDisplacement_getElem (h : ℕ) (w : List SignedStep) (i : ℕ) (hi : i < w.length) :
    wordStepDisplacement h w i = w[i].displacement h := by
  simp [wordStepDisplacement, List.getElem?_eq_getElem hi]

lemma tuplePrime_dvd_step {h p i : ℕ} {w : List SignedStep} (hp : TuplePrimeAt w p i) :
    (p : ℤ) ∣ wordStepDisplacement h w i := by
  have hi := hp.index_lt
  have hpd := ((tuplePrimeAt_iff_getElem w p i hi).mp hp).2
  have hcast : (p : ℤ) ∣ (w[i].tuple : ℤ) := by exact_mod_cast hpd
  rw [wordStepDisplacement_getElem h w i hi]
  exact (hcast.mul_left (w[i].padding : ℤ)).trans (w[i].divisor_dvd_displacement h)

/-- Positivity supplies each tuple-prime divisibility at the exact prefix sum. -/
lemma PositiveWord.tuplePrime_departure {h p i : ℕ} {x : ℤ} {w : List SignedStep}
    (hw : PositiveWord h x w) (hp : TuplePrimeAt w p i) :
    (p : ℤ) ∣ x + wordDisplacement h (w.take i) := by
  induction w generalizing x i with
  | nil => simp [TuplePrimeAt] at hp
  | cons a w ih =>
      rcases hw with ⟨ha, hw⟩
      cases i with
      | zero =>
          have hp' := (tuplePrimeAt_iff_getElem (a :: w) p 0 (by simp)).mp hp
          have hcast : (p : ℤ) ∣ (a.tuple : ℤ) := by exact_mod_cast hp'.2
          simpa only [List.take_zero, wordDisplacement_nil, add_zero] using
            (hcast.mul_left (a.padding : ℤ)).trans ha
      | succ i =>
          have hp' : TuplePrimeAt w p i := by simpa [TuplePrimeAt] using hp
          simpa only [List.take_succ_cons, wordDisplacement_cons, add_assoc] using ih hw hp'

lemma PositiveWord.tuplePrime_departure_sum {h : ℕ} {x : ℤ} {w : List SignedStep}
    (hw : PositiveWord h x w) : ∀ p i, i < w.length → TuplePrimeAt w p i →
      (p : ℤ) ∣ x + ∑ a ∈ range i, wordStepDisplacement h w a := by
  intro p i _ hp
  rw [← wordDisplacement_take]
  exact hw.tuplePrime_departure hp

/-- Equal-size squarefree whole tuples cannot change by merely adding primes:
a changed tuple loses at least one prime from the preceding tuple. -/
lemma adjacent_tuple_prime_change (w : List SignedStep) (J : ℕ)
    (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple)) :
    ∀ i, i + 1 < w.length → ∃ p, TuplePrimeAt w p i ∧ ¬TuplePrimeAt w p (i + 1) := by
  intro i hi
  have hi0 : i < w.length := by omega
  have ha := List.getElem_mem hi0
  have hb := List.getElem_mem hi
  have hneq : w[i].tuple ≠ w[i + 1].tuple := (List.isChain_iff_getElem.mp hchain) i hi
  have hsets : w[i].tuple.primeFactors ≠ w[i + 1].tuple.primeFactors := by
    intro heq
    apply hneq
    calc
      _ = ∏ p ∈ w[i].tuple.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hsq _ ha)).symm
      _ = ∏ p ∈ w[i + 1].tuple.primeFactors, p := by rw [heq]
      _ = _ := Nat.prod_primeFactors_of_squarefree (hsq _ hb)
  have hnot : ¬w[i].tuple.primeFactors ⊆ w[i + 1].tuple.primeFactors := by
    intro hsub
    apply hsets
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard _ ha, hcard _ hb])
  obtain ⟨p, hpa, hpb⟩ := Finset.not_subset.mp hnot
  have hp := Nat.mem_primeFactors.mp hpa
  refine ⟨p, (tuplePrimeAt_iff_getElem w p i hi0).mpr ⟨hp.1, hp.2.1⟩, ?_⟩
  intro hpi
  have hpbi := (tuplePrimeAt_iff_getElem w p (i + 1) hi).mp hpi
  exact hpb (Nat.mem_primeFactors.mpr ⟨hpbi.1, hpbi.2, (hsq _ hb).ne_zero⟩)

/-- Every tuple prime is coprime to the common multiplier and every padding.
Consequently an absent tuple prime cannot divide a step's displacement. -/
lemma word_prime_support {h : ℕ} {w : List SignedStep}
    (hsupport : ∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ a ∈ w, ¬p ∣ a.padding) :
    ∀ p i, (∃ j, j < w.length ∧ TuplePrimeAt w p j) → i < w.length →
      ¬TuplePrimeAt w p i → ¬(p : ℤ) ∣ wordStepDisplacement h w i := by
  intro p i hseen hi hnot
  obtain ⟨j, _, hpj⟩ := hseen
  have hp := hpj.1
  have hdata := hsupport p j hpj
  have ha := List.getElem_mem hi
  have htuple : ¬p ∣ w[i].tuple := by
    intro hdiv
    exact hnot ((tuplePrimeAt_iff_getElem w p i hi).mpr ⟨hp, hdiv⟩)
  rw [wordStepDisplacement_getElem h w i hi]
  exact w[i].prime_not_dvd_displacement h p hp hdata.1 (hdata.2 _ ha) htuple

lemma word_step_nonzero {h : ℕ} {w : List SignedStep} (hh : 0 < h)
    (hq : ∀ a ∈ w, 0 < a.padding) (hd : ∀ a ∈ w, Squarefree a.tuple) :
    ∀ i, i < w.length → wordStepDisplacement h w i ≠ 0 := by
  intro i hi
  rw [wordStepDisplacement_getElem h w i hi]
  have ha := List.getElem_mem hi
  have hq' : (w[i].padding : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hq _ ha))
  have hd' : (w[i].tuple : ℤ) ≠ 0 := by exact_mod_cast (hd _ ha).ne_zero
  have hh' : (h : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  unfold SignedStep.displacement
  split <;> simp_all

/-- The block-interval lemma for actual signed words. All hypotheses concern
admissibility, positivity, survival, or the explicit prime supports. Neither
interval-shaped occurrences nor nonzero subintervals is assumed. -/
theorem PositiveWord.block_geometry {h s J : ℕ} {supply : ℕ → ℕ → Prop}
    {x : ℤ} {w : List SignedStep} (hw : PositiveWord h x w) (hh : 0 < h)
    (hlen : w.length ≤ s) (heligible : ∀ a ∈ w, supply a.tuple a.padding)
    (hq : ∀ a ∈ w, 0 < a.padding) (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ a ∈ w, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x w y → ¬ProhibitedSite h s supply y) :
    TuplePrimeIntervals w ∧
      ∀ a b, a < b → b ≤ w.length → wordDisplacement h (wordSlice w a b) ≠ 0 := by
  have havoid := hw.avoids_prohibitedIntervals hsurvive hlen heligible hchain
  have hinterval := block_occurrence_intervals (TuplePrimeAt w) (wordStepDisplacement h w)
    id x w.length hw.tuplePrime_departure_sum (fun _ _ _ hp => tuplePrime_dvd_step hp)
    (word_prime_support hsupport) havoid
  refine ⟨?_, ?_⟩
  · intro p i j k hij hjk hk hpi hpk
    exact hinterval p i j k (Nat.zero_le _) hij hjk hk hpi hpk
  · intro a b hab hbw
    rw [wordSlice_displacement h w hab.le]
    exact block_nonzero_subintervals (TuplePrimeAt w) (wordStepDisplacement h w) id w.length
      hinterval (fun _ _ _ hp => tuplePrime_dvd_step hp) (word_prime_support hsupport)
      (word_step_nonzero hh hq hsq) (adjacent_tuple_prime_change w J hsq hcard hchain)
      havoid a b hab hbw

end TwoPointCorrelations

end OAI

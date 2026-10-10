import OAI.NumberTheory.TwoPoint.Bounds.LitOccurrenceWeights

namespace OAI

/-! Counts of the actual slots belonging to each prime label. -/

namespace TwoPointCorrelations

open Finset

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

def labelOccurrences (label : τ → ι) (i : ι) : Finset τ :=
  univ.filter (fun t => label t = i)

def litOccurrences (label : τ → ι) (lit : τ → Bool) (i : ι) : Finset τ :=
  (labelOccurrences label i).filter (fun t => lit t = true)

def unlitOccurrences (label : τ → ι) (lit : τ → Bool) (i : ι) : Finset τ :=
  (labelOccurrences label i).filter (fun t => lit t = false)

omit [Fintype ι] in
lemma lit_unlit_count (label : τ → ι) (lit : τ → Bool) (i : ι) :
    (litOccurrences label lit i).card + (unlitOccurrences label lit i).card =
      (labelOccurrences label i).card := by
  have he : unlitOccurrences label lit i =
      (labelOccurrences label i).filter (fun t => ¬lit t = true) := by
    ext t
    simp [unlitOccurrences]
  rw [litOccurrences, he]
  exact card_filter_add_card_filter_not (s := labelOccurrences label i) (fun t => lit t = true)

lemma total_label_occurrences (label : τ → ι) :
    ∑ i, (labelOccurrences label i).card = Fintype.card τ := by
  simpa only [labelOccurrences, mem_univ, filter_true, card_univ] using
    sum_card_fiberwise_eq_card_filter (univ : Finset τ) (univ : Finset ι) label

def singletonLabels (label : τ → ι) : Finset ι :=
  univ.filter (fun i => (labelOccurrences label i).card = 1)

def nonsingletonLabels (label : τ → ι) : Finset ι :=
  univ.filter (fun i => 2 ≤ (labelOccurrences label i).card)

/-- The number of labels is at most half the slot count plus half the
singleton count. All labels here are observed in the word. -/
lemma twice_labels_le_slots_add_singletons (label : τ → ι)
    (hused : ∀ i, 0 < (labelOccurrences label i).card) :
    2 * Fintype.card ι ≤ Fintype.card τ + (singletonLabels label).card := by
  have hlocal (i : ι) : 2 ≤ (labelOccurrences label i).card +
      (if (labelOccurrences label i).card = 1 then 1 else 0) := by
    have hi := hused i
    split_ifs <;> omega
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hlocal i)
  rw [sum_add_distrib, total_label_occurrences] at hs
  have hc : (∑ i : ι, if (labelOccurrences label i).card = 1 then (1 : ℕ) else 0) =
      (singletonLabels label).card := by simp [singletonLabels, sum_boole]
  rw [hc] at hs
  simpa [mul_comm] using hs

/-- The extra-exponent bound applies to the literal occurrence counts of
every nonsingleton in the given designation. -/
lemma actual_unlit_le_twice_extra (label : τ → ι) (lit : τ → Bool) :
    (∑ i : nonsingletonLabels label, (unlitOccurrences label lit i.val).card) ≤
      2 * ∑ i : nonsingletonLabels label,
        extraReciprocalExponent (litOccurrences label lit i.val).card
          (unlitOccurrences label lit i.val).card := by
  apply total_unlit_le_twice_extra
  intro i
  rw [lit_unlit_count]
  exact (mem_filter.mp i.property).2

end TwoPointCorrelations

end OAI

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace OAI

namespace Balanced.RepeatedIncidences

open scoped BigOperators

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

def multiplicity (A : ι → Finset α) (s : Finset ι) (a : α) : ℕ :=
  (s.filter fun i => a ∈ A i).card

def reuse (A : ι → Finset α) (s : Finset ι) : ℕ :=
  (∑ i ∈ s, (A i).card) - (s.biUnion A).card

omit [DecidableEq ι] in

theorem sum_multiplicity (A : ι → Finset α) (s : Finset ι) :
    (∑ a ∈ s.biUnion A, multiplicity A s a) = ∑ i ∈ s, (A i).card := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun i a => a ∈ A i) (s := s) (t := s.biUnion A)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at h
  unfold multiplicity
  rw [← h]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ext a
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro ha
    exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, ha⟩, ha⟩

omit [DecidableEq ι] in
theorem multiplicity_pos (A : ι → Finset α) (s : Finset ι) {a : α}
    (ha : a ∈ s.biUnion A) : 1 ≤ multiplicity A s a := by
  obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩

omit [DecidableEq ι] in

theorem reuse_eq_sum (A : ι → Finset α) (s : Finset ι) :
    reuse A s = ∑ a ∈ s.biUnion A, (multiplicity A s a - 1) := by
  rw [Finset.sum_tsub_distrib _ (fun a ha => multiplicity_pos A s ha)]
  simp [sum_multiplicity, reuse]

theorem mem_inter_rest_iff (A : ι → Finset α) (s : Finset ι)
    {i : ι} (hi : i ∈ s) {a : α} :
    a ∈ A i ∩ (s.erase i).biUnion A ↔ a ∈ A i ∧ 2 ≤ multiplicity A s a := by
  constructor
  · intro ha
    obtain ⟨hai, har⟩ := Finset.mem_inter.mp ha
    obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp har
    refine ⟨hai, Finset.one_lt_card.mpr ?_⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩, j,
      Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hj).2, haj⟩,
      (Finset.mem_erase.mp hj).1.symm⟩
  · rintro ⟨hai, hm⟩
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hm
    apply Finset.mem_inter.mpr
    refine ⟨hai, ?_⟩
    by_cases hji : j = i
    · subst j
      exact Finset.mem_biUnion.mpr ⟨k,
        Finset.mem_erase.mpr ⟨hjk.symm, (Finset.mem_filter.mp hk).1⟩,
        (Finset.mem_filter.mp hk).2⟩
    · exact Finset.mem_biUnion.mpr ⟨j,
        Finset.mem_erase.mpr ⟨hji, (Finset.mem_filter.mp hj).1⟩,
        (Finset.mem_filter.mp hj).2⟩

theorem sum_inter_rest (A : ι → Finset α) (s : Finset ι) :
    (∑ i ∈ s, (A i ∩ (s.erase i).biUnion A).card) =
      ∑ a ∈ s.biUnion A, if 2 ≤ multiplicity A s a then multiplicity A s a else 0 := by
  let r : ι → α → Prop := fun i a => a ∈ A i ∧ 2 ≤ multiplicity A s a
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := s) (t := s.biUnion A)
  calc
    (∑ i ∈ s, (A i ∩ (s.erase i).biUnion A).card) =
        ∑ i ∈ s, ((s.biUnion A).filter (r i)).card := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      ext a
      rw [mem_inter_rest_iff A s hi]
      simp only [Finset.mem_filter, r]
      constructor
      · intro ha
        exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, ha.1⟩, ha⟩
      · exact fun ha => ha.2
    _ = ∑ a ∈ s.biUnion A, (s.filter fun i => r i a).card := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hm : 2 ≤ multiplicity A s a
      · simp only [r, hm, and_true, ite_true]
        rfl
      · simp only [r, hm, and_false, Finset.filter_false, Finset.card_empty, ite_false]

theorem sum_inter_rest_le_twice_reuse (A : ι → Finset α) (s : Finset ι) :
    (∑ i ∈ s, (A i ∩ (s.erase i).biUnion A).card) ≤ 2 * reuse A s := by
  rw [sum_inter_rest, reuse_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hm : 2 ≤ multiplicity A s a
  · simp only [ite_eq_left hm]
    omega
  · simp only [ite_eq_right hm]
    omega

end Balanced.RepeatedIncidences

end OAI

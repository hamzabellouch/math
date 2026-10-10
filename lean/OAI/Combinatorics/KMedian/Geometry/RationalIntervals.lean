import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
namespace RationalIntervals

def height (Q : Finset ℚ) : ℚ := (insert 0 Q).max' (insert_nonempty _ _)
def previous (Q : Finset ℚ) (q : ℚ) : ℚ := height (Q.filter (fun p => p<q))
def length (Q : Finset ℚ) (q : ℚ) : ℚ := q-previous Q q

theorem height_nonneg (Q : Finset ℚ) : 0 ≤ height Q :=
  le_max' _ _ (mem_insert_self _ _)

theorem height_eq (Q : Finset ℚ) (q : ℚ) (hq : q ∈ Q) (hq0 : 0 ≤ q)
    (hmax : ∀ p ∈ Q, p ≤ q) : height Q=q := by
  apply le_antisymm
  · apply max'_le
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact hq0
    · exact hmax p hp
  · exact le_max' _ _ (mem_insert_of_mem hq)

theorem previous_lt (Q : Finset ℚ) {q : ℚ} (hq : 0 < q) : previous Q q < q := by
  have hm := max'_mem (insert 0 (Q.filter (fun p => p<q))) (insert_nonempty _ _)
  rcases mem_insert.mp hm with he | hm
  · rw [show previous Q q=0 from he]; exact hq
  · exact (mem_filter.mp hm).2

theorem length_pos (Q : Finset ℚ) {q : ℚ} (hq : 0 < q) : 0 < length Q q :=
  sub_pos.mpr (previous_lt Q hq)

theorem length_le (Q : Finset ℚ) (q : ℚ) : length Q q ≤ q :=
  sub_le_self _ (height_nonneg _)

theorem previous_erase_max (Q : Finset ℚ) {a q : ℚ} (hqa : q ≤ a) :
    previous (Q.erase a) q=previous Q q := by
  unfold previous
  congr 1
  ext p
  simp only [mem_filter,mem_erase]
  constructor
  · rintro ⟨⟨_,hp⟩,hpq⟩; exact ⟨hp,hpq⟩
  · rintro ⟨hp,hpq⟩
    exact ⟨⟨ne_of_lt (hpq.trans_le hqa),hp⟩,hpq⟩

theorem sum_lengths (Q : Finset ℚ) (hQ : ∀ q ∈ Q, 0 < q) :
    (∑ q ∈ Q, length Q q)=height Q := by
  revert hQ
  refine Q.strongInductionOn ?_
  intro Q ih hQ
  by_cases hne : Q.Nonempty
  · let a := Q.max' hne
    have ha : a ∈ Q := max'_mem Q hne
    have hamax : ∀ q ∈ Q, q ≤ a := fun q hq => le_max' Q q hq
    have hheight : height Q=a := height_eq Q a ha (hQ a ha).le hamax
    have hprev : previous Q a=height (Q.erase a) := by
      unfold previous
      congr 1
      ext q
      simp only [mem_filter,mem_erase]
      constructor
      · rintro ⟨hq,hqa⟩; exact ⟨ne_of_lt hqa,hq⟩
      · rintro ⟨hne,hq⟩; exact ⟨hq,lt_of_le_of_ne (hamax q hq) hne⟩
    have hsum := ih (Q.erase a) (erase_ssubset ha) (fun q hq => hQ q (mem_of_mem_erase hq))
    have hold : ∀ q ∈ Q.erase a, length Q q=length (Q.erase a) q := by
      intro q hq
      rw [length,length,previous_erase_max Q (hamax q (mem_of_mem_erase hq))]
    rw [← sum_erase_add Q (length Q) ha,sum_congr rfl hold,hsum,length,hprev,hheight]
    ring
  · have he := not_nonempty_iff_eq_empty.mp hne
    subst Q
    simp [height]

theorem previous_filter_le (Q : Finset ℚ) {b q : ℚ} (hqb : q ≤ b) :
    previous (Q.filter (fun p => p ≤ b)) q=previous Q q := by
  unfold previous
  congr 1
  ext p
  simp only [mem_filter]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,(h.2.trans_le hqb).le⟩,h.2⟩⟩

theorem prefix_sum (Q : Finset ℚ) (hQ : ∀ q ∈ Q, 0 < q) {b : ℚ}
    (hb : b=0 ∨ b ∈ Q) :
    (∑ q ∈ Q.filter (fun p => p ≤ b), length Q q)=b := by
  rcases hb with rfl | hb
  · have he : Q.filter (fun p => p ≤ 0)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro q hq hq0
      exact not_le_of_gt (hQ q hq) hq0
    rw [he,sum_empty]
  · calc
      _ = ∑ q ∈ Q.filter (fun p => p ≤ b), length (Q.filter (fun p => p ≤ b)) q := by
        apply sum_congr rfl
        intro q hq
        rw [length,length,previous_filter_le Q (mem_filter.mp hq).2]
      _ = height (Q.filter (fun p => p ≤ b)) :=
        sum_lengths _ (fun q hq => hQ q (mem_filter.mp hq).1)
      _ = b := height_eq _ b (mem_filter.mpr ⟨hb,le_rfl⟩) (hQ b hb).le
        (fun q hq => (mem_filter.mp hq).2)

end RationalIntervals
end MetricKMedian.Preparation
end
end

end OAI

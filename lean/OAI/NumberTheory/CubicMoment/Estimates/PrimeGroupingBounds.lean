import OAI.NumberTheory.CubicMoment.Estimates.PrimeGrouping

namespace OAI

/-! Short-side exponent bounds obtained by actual subset grouping.
The upper-height case permits one prime longer than two thirds. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma prime_exponent_closed_group {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i ∧ a i ≤ 2/3)
    (hsum : ∑ i ∈ s, a i = 1) :
    ∃ t ⊆ s, 1/3 ≤ ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i ≤ 2/3 := by
  classical
  by_cases heq : ∃ i ∈ s, a i = 2/3
  · obtain ⟨i,hi,hai⟩ := heq
    refine ⟨{i},Finset.singleton_subset_iff.mpr hi,?_,?_⟩ <;> norm_num [hai]
  have hlt : ∀ i ∈ s, 0 < a i ∧ a i < 2/3 := by
    intro i hi
    exact ⟨(ha i hi).1,lt_of_le_of_ne (ha i hi).2 (fun h => heq ⟨i,hi,h⟩)⟩
  rcases prime_exponent_partition s a hlt hsum with ⟨t,ht,hlo,hhi⟩ | ⟨hcard,hthird⟩
  · exact ⟨t,ht,hlo.le,hhi.le⟩
  · obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    refine ⟨{i},Finset.singleton_subset_iff.mpr hi,?_,?_⟩ <;> norm_num [hthird i hi]

/-- For the upper-height branch, a prime may exceed two thirds. The
known complementary exponent lower bound still supplies a short side. -/
theorem prime_exponent_short_group {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) {σ : ℝ} (_hσ : 0 < σ) (hσ₁ : σ ≤ 1/3)
    (ha : ∀ i ∈ s, 0 < a i ∧ a i ≤ 1-σ)
    (hsum : ∑ i ∈ s, a i = 1) :
    ∃ t ⊆ s, σ ≤ ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i ≤ 1/2 := by
  classical
  by_cases hbig : ∃ i ∈ s, 2/3 < a i
  · obtain ⟨i,hi,hai⟩ := hbig
    refine ⟨s.erase i,Finset.erase_subset _ _,?_,?_⟩
    all_goals have he := Finset.sum_erase_add s a hi
    · linarith [(ha i hi).2]
    · linarith
  · have hsmall : ∀ i ∈ s, 0 < a i ∧ a i ≤ 2/3 := by
      intro i hi
      exact ⟨(ha i hi).1,le_of_not_gt (fun h => hbig ⟨i,hi,h⟩)⟩
    obtain ⟨t,ht,hlo,hhi⟩ := prime_exponent_closed_group s a hsmall hsum
    by_cases hhalf : (∑ i ∈ t, a i) ≤ 1/2
    · exact ⟨t,ht,hσ₁.trans hlo,hhalf⟩
    · refine ⟨s\t,Finset.sdiff_subset,?_,?_⟩
      all_goals have he := Finset.sum_sdiff ht (f := a)
      · rw [hsum] at he
        linarith
      · rw [hsum] at he
        linarith [not_le.mp hhalf]

end CubicFirstMoment

end

end OAI

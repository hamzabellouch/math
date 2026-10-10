import Mathlib

namespace OAI

/-! The exact partition alternative behind the large-distinguished-
factor branch of the manuscript's prime decomposition. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- A partition of one with each part below two thirds either has a
strictly interior subset sum or consists of exactly three equal thirds. -/
theorem prime_exponent_partition {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i ∧ a i < 2/3)
    (hsum : ∑ i ∈ s, a i = 1) :
    (∃ t ⊆ s, 1/3 < ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i < 2/3) ∨
      (s.card = 3 ∧ ∀ i ∈ s, a i = 1/3) := by
  classical
  by_cases hex : ∃ t ⊆ s, 1/3 < ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i < 2/3
  · exact Or.inl hex
  right
  have hno (t : Finset ι) (ht : t ⊆ s) (hlo : 1/3 < ∑ i ∈ t, a i) :
      2/3 ≤ ∑ i ∈ t, a i :=
    le_of_not_gt (fun hhi => hex ⟨t,ht,hlo,hhi⟩)
  have hthird (i : ι) (hi : i ∈ s) : a i ≤ 1/3 := by
    by_contra h
    have hh := hno {i} (Finset.singleton_subset_iff.mpr hi) (by simpa using not_le.mp h)
    have hh' : 2/3 ≤ a i := by simpa using hh
    exact (not_le_of_gt (ha i hi).2) hh'
  have hall (i : ι) (hi : i ∈ s) : a i = 1/3 := by
    by_contra heq
    have hai : a i < 1/3 := lt_of_le_of_ne (hthird i hi) heq
    let T := s.powerset.filter (fun t => i ∈ t ∧ 1/3 < ∑ j ∈ t, a j)
    have hT : T.Nonempty := by
      refine ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl s),hi,?_⟩⟩
      rw [hsum]
      norm_num
    obtain ⟨t,ht,htmin⟩ := T.exists_min_image Finset.card hT
    have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have hit : i ∈ t := (Finset.mem_filter.mp ht).2.1
    have htlarge : 1/3 < ∑ j ∈ t, a j := (Finset.mem_filter.mp ht).2.2
    obtain ⟨j,hjt,hji⟩ : ∃ j ∈ t, j ≠ i := by
      by_contra! h
      have he : t = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hit,h⟩
      rw [he,Finset.sum_singleton] at htlarge
      linarith
    have hjs : j ∈ s := hts hjt
    have herase : ∑ k ∈ t.erase j, a k ≤ 1/3 := by
      by_contra h
      have hmem : t.erase j ∈ T := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.erase_subset j t).trans hts),
          Finset.mem_erase.mpr ⟨hji.symm,hit⟩,not_le.mp h⟩
      have hle := htmin _ hmem
      have hlt := Finset.card_erase_lt_of_mem hjt
      omega
    have hsplit := Finset.sum_erase_add t a hjt
    have htupper : ∑ k ∈ t, a k ≤ 2/3 := by linarith [hthird j hjs]
    have hteq : ∑ k ∈ t, a k = 2/3 := le_antisymm htupper (hno t hts htlarge)
    have haj : a j = 1/3 := by linarith [hthird j hjs]
    have hpairs : ({i,j}:Finset ι) ⊆ s := by simp [Finset.insert_subset_iff,hi,hjs]
    have hpairsum : (∑ k ∈ ({i,j}:Finset ι), a k) = a i+a j := by
      simp [hji.symm]
    have hpair := hno {i,j} hpairs (by rw [hpairsum,haj]; linarith [(ha i hi).1])
    rw [hpairsum,haj] at hpair
    linarith
  refine ⟨?_,hall⟩
  have hconst : (∑ i ∈ s, a i) = ∑ _i ∈ s, (1/3:ℝ) :=
    Finset.sum_congr rfl hall
  have hcard : (s.card:ℝ)*(1/3) = 1 := by simpa only [Finset.sum_const,nsmul_eq_mul] using hconst.symm.trans hsum
  have hc : (s.card:ℝ) = 3 := by linarith
  exact_mod_cast hc

end CubicFirstMoment

end

end OAI

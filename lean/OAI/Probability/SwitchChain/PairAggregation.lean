import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairAggregation

variable {V : Type*} [DecidableEq V]

lemma card_union_of_pairs {a b : Finset V} (ha : a.card = 2) (hb : b.card = 2)
    (hne : a ≠ b) (hnd : ¬ Disjoint a b) : (a ∪ b).card = 3 := by
  have hi_pos : 0 < (a ∩ b).card := by
    apply Finset.card_pos.mpr
    exact Finset.not_disjoint_iff_nonempty_inter.mp hnd
  have hi_le : (a ∩ b).card ≤ 2 := by
    simpa [ha] using Finset.card_le_card (Finset.inter_subset_left : a ∩ b ⊆ a)
  have hi_ne : (a ∩ b).card ≠ 2 := by
    intro hi
    have hia : a ∩ b = a := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hab : a ⊆ b := by rw [← hia]; exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hab (by omega))
  have h := Finset.card_union_add_card_inter a b
  omega

lemma triple_incidence_count (s a b : Finset V) (ha : a.card = 2) (hb : b.card = 2)
    (has : a ⊆ s) (hbs : b ⊆ s) :
    ((s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T)).card =
      if a = b then s.card - 2 else if Disjoint a b then 0 else 1 := by
  have hfilter : (s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T) =
      (s.powersetCard 3).filter (a ∪ b ⊆ ·) := by
    ext T
    simp only [Finset.mem_filter, Finset.union_subset_iff]
  rw [hfilter]
  by_cases hab : a = b
  · subst b
    simp only [Finset.union_self]
    rw [Finset.card_filter_powersetCard_subset a s 3 has (by omega), ha]
    simp
  · simp only [ite_eq_right hab]
    by_cases hd : Disjoint a b
    · rw [ite_eq_left hd]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hT, huT⟩ := Finset.mem_filter.mp hT
      have hcard := Finset.card_le_card huT
      have hTu := (Finset.mem_powersetCard.mp hT).2
      have hu := Finset.card_union_of_disjoint hd
      omega
    · rw [ite_eq_right hd]
      have hu := card_union_of_pairs ha hb hab hd
      rw [Finset.card_filter_powersetCard_subset (a ∪ b) s 3
        (Finset.union_subset has hbs) (by omega), hu]
      simp

lemma sum_triple_incidence (s : Finset V) (B : Finset V → Finset V → ℝ) :
    (∑ T ∈ s.powersetCard 3, ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
    ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      (((s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T)).card : ℝ) * B a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_filter]
  simp

lemma triple_expansion (s : Finset V) (hs : 3 ≤ s.card)
    (B : Finset V → Finset V → ℝ) :
    (∑ T ∈ s.powersetCard 3, ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
    (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b) +
      (s.card - 3 : ℕ) * (∑ a ∈ s.powersetCard 2, B a a) -
      (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
        if Disjoint a b then B a b else 0) := by
  rw [sum_triple_incidence]
  have hpoint : ∀ a ∈ s.powersetCard 2, ∀ b ∈ s.powersetCard 2,
      (((s.powersetCard 3).filter (fun T => a ⊆ T ∧ b ⊆ T)).card : ℝ) * B a b =
        B a b + (if a = b then (s.card - 3 : ℕ) * B a b else 0) -
          (if Disjoint a b then B a b else 0) := by
    intro a ha b hb
    obtain ⟨has, ha⟩ := Finset.mem_powersetCard.mp ha
    obtain ⟨hbs, hb⟩ := Finset.mem_powersetCard.mp hb
    rw [triple_incidence_count s a b ha hb has hbs]
    by_cases he : a = b
    · subst b
      have hnd : ¬ Disjoint a a := by
        intro hd
        have he := disjoint_self.mp hd
        simp [he] at ha
      simp only [ite_eq_right hnd]
      have hc : s.card - 2 = (s.card - 3) + 1 := by omega
      rw [hc]
      push_cast
      ring
    · by_cases hd : Disjoint a b <;> simp [he, hd]
  simp_rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (hpoint a ha))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp [ha]

lemma sum_pair_terms_over_triples (s : Finset V) (h : Finset V → ℝ) :
    (∑ T ∈ s.powersetCard 3, ∑ a ∈ s.powersetCard 2,
      if a ⊆ T then h a else 0) =
      (s.card - 2 : ℕ) * (∑ a ∈ s.powersetCard 2, h a) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨has, ha⟩ := Finset.mem_powersetCard.mp ha
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_filter_powersetCard_subset a s 3 has (by omega), ha]
  simp

theorem global_of_local_ambient (s : Finset V) (hs : 3 ≤ s.card)
    (h : Finset V → ℝ) (B : Finset V → Finset V → ℝ)
    (hdiag : ∀ a ∈ s.powersetCard 2, B a a = h a)
    (htriple : ∀ T ∈ s.powersetCard 3,
      (∑ a ∈ s.powersetCard 2, if a ⊆ T then h a else 0) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
        if a ⊆ T ∧ b ⊆ T then B a b else 0)
    (hdisjoint : 0 ≤ ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if Disjoint a b then B a b else 0) :
    (∑ a ∈ s.powersetCard 2, h a) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b := by
  have hsum := Finset.sum_le_sum htriple
  rw [sum_pair_terms_over_triples, triple_expansion s hs] at hsum
  have hd : (∑ a ∈ s.powersetCard 2, B a a) =
      ∑ a ∈ s.powersetCard 2, h a := Finset.sum_congr rfl hdiag
  rw [hd] at hsum
  have hc : s.card - 2 = (s.card - 3) + 1 := by omega
  rw [hc] at hsum
  push_cast at hsum
  nlinarith

lemma pairSum_restrict (s T : Finset V) (hTs : T ⊆ s) (f : Finset V → ℝ) :
    (∑ a ∈ s.powersetCard 2, if a ⊆ T then f a else 0) =
      ∑ a ∈ T.powersetCard 2, f a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨has, ha⟩, haT⟩
    exact ⟨haT, ha⟩
  · rintro ⟨haT, ha⟩
    exact ⟨⟨haT.trans hTs, ha⟩, haT⟩

lemma local_quadratic_restrict (s T : Finset V) (hTs : T ⊆ s)
    (B : Finset V → Finset V → ℝ) :
    (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
      ∑ a ∈ T.powersetCard 2, ∑ b ∈ T.powersetCard 2, B a b := by
  have he : (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if a ⊆ T ∧ b ⊆ T then B a b else 0) =
      ∑ a ∈ s.powersetCard 2, if a ⊆ T then
        (∑ b ∈ s.powersetCard 2, if b ⊆ T then B a b else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases haT : a ⊆ T <;> simp [haT]
  rw [he, pairSum_restrict s T hTs]
  apply Finset.sum_congr rfl
  intro a ha
  exact pairSum_restrict s T hTs (B a)

theorem global_of_local (s : Finset V) (hs : 3 ≤ s.card)
    (h : Finset V → ℝ) (B : Finset V → Finset V → ℝ)
    (hdiag : ∀ a ∈ s.powersetCard 2, B a a = h a)
    (htriple : ∀ T ∈ s.powersetCard 3,
      (∑ a ∈ T.powersetCard 2, h a) ≤
      ∑ a ∈ T.powersetCard 2, ∑ b ∈ T.powersetCard 2, B a b)
    (hdisjoint : 0 ≤ ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if Disjoint a b then B a b else 0) :
    (∑ a ∈ s.powersetCard 2, h a) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b := by
  apply global_of_local_ambient s hs h B hdiag _ hdisjoint
  intro T hT
  have hTs := (Finset.mem_powersetCard.mp hT).1
  rw [pairSum_restrict s T hTs, local_quadratic_restrict s T hTs]
  exact htriple T hT

end Problem315.PairAggregation

end

end OAI

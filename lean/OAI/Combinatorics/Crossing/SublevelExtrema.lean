import OAI.Combinatorics.Crossing.FirstLastVisits

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem sublevel_passage_extrema (f : ℝ → ℝ) (hf : Continuous f) (r τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hvisit : f τ < r) :
    ∃ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) 1 ∧
      a ≤ τ ∧ τ ≤ b ∧ f a ≤ r ∧ f b ≤ r ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ r → a ≤ t ∧ t ≤ b) ∧
      (0 < a → f a=r) ∧ (b < 1 → f b=r) ∧
      (0 < τ → a < τ) ∧ (τ < 1 → τ < b) := by
  let S : Set ℝ := Set.Icc 0 1 ∩ {t | f t ≤ r}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hτS : τ ∈ S := ⟨hτ,hvisit.le⟩
  obtain ⟨a,ha⟩ := hS.exists_isLeast ⟨τ,hτS⟩
  obtain ⟨b,hb⟩ := hS.exists_isGreatest ⟨τ,hτS⟩
  have hfa (ha0 : 0 < a) : f a=r := by
    have hf0 : r < f 0 := by
      apply lt_of_not_ge
      intro h
      have hh := ha.2 (show (0 : ℝ) ∈ S from ⟨⟨le_rfl,zero_le_one⟩,h⟩)
      linarith
    apply le_antisymm ha.1.2
    by_contra hn
    have hlt : f a < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' ha.1.1.1 hf.continuousOn ⟨hlt.le,hf0.le⟩
    have hmem : t ∈ S := ⟨⟨ht.1,ht.2.trans ha.1.1.2⟩,he.le⟩
    have hta : t=a := le_antisymm ht.2 (ha.2 hmem)
    rw [hta] at he
    exact hlt.ne he
  have hfb (hb1 : b < 1) : f b=r := by
    have hf1 : r < f 1 := by
      apply lt_of_not_ge
      intro h
      have hh := hb.2 (show (1 : ℝ) ∈ S from ⟨⟨zero_le_one,le_rfl⟩,h⟩)
      linarith
    apply le_antisymm hb.1.2
    by_contra hn
    have hlt : f b < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hb.1.1.2 hf.continuousOn ⟨hlt.le,hf1.le⟩
    have hmem : t ∈ S := ⟨⟨hb.1.1.1.trans ht.1,ht.2⟩,he.le⟩
    have htb : t=b := le_antisymm (hb.2 hmem) ht.1
    rw [htb] at he
    exact hlt.ne he
  refine ⟨a,b,ha.1.1,hb.1.1,ha.2 hτS,hb.2 hτS,ha.1.2,hb.1.2,
    fun t ht hh => ⟨ha.2 ⟨ht,hh⟩,hb.2 ⟨ht,hh⟩⟩,hfa,hfb,?_,?_⟩
  · intro ht0
    apply lt_of_le_of_ne (ha.2 hτS)
    intro he
    have h := hfa (he.symm ▸ ht0)
    rw [he] at h
    exact hvisit.ne h
  · intro ht1
    apply lt_of_le_of_ne (hb.2 hτS)
    intro he
    have h := hfb (he ▸ ht1)
    rw [← he] at h
    exact hvisit.ne h

end Zarankiewicz

end

end OAI

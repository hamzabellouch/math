import OAI.Combinatorics.Crossing.MarkedCurveDisks
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem first_last_sublevel_visits (f : ℝ → ℝ) (hf : Continuous f) (r τ : ℝ)
    (h0 : r < f 0) (h1 : r < f 1) (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (hvisit : f τ < r) :
    ∃ a b : ℝ, 0 < a ∧ a < τ ∧ τ < b ∧ b < 1 ∧ f a=r ∧ f b=r ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ r → a ≤ t ∧ t ≤ b) := by
  let S : Set ℝ := Set.Icc 0 1 ∩ {t | f t ≤ r}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hne : S.Nonempty := ⟨τ,⟨hτ.1.le,hτ.2.le⟩,hvisit.le⟩
  obtain ⟨a,ha⟩ := hS.exists_isLeast hne
  obtain ⟨b,hb⟩ := hS.exists_isGreatest hne
  have ha0 : 0 < a := lt_of_le_of_ne ha.1.1.1 (by
    intro he
    have hh := ha.1.2
    rw [← he] at hh
    exact (not_le_of_gt h0) hh)
  have hb1 : b < 1 := lt_of_le_of_ne hb.1.1.2 (by
    intro he
    have hh := hb.1.2
    rw [he] at hh
    exact (not_le_of_gt h1) hh)
  have hfa : f a=r := by
    apply le_antisymm ha.1.2
    by_contra hn
    have hlt : f a < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' ha.1.1.1 hf.continuousOn ⟨hlt.le,h0.le⟩
    have hmem : t ∈ S := ⟨⟨ht.1,ht.2.trans ha.1.1.2⟩,he.le⟩
    have hta : t=a := le_antisymm ht.2 (ha.2 hmem)
    rw [hta] at he
    exact hlt.ne he
  have hfb : f b=r := by
    apply le_antisymm hb.1.2
    by_contra hn
    have hlt : f b < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hb.1.1.2 hf.continuousOn ⟨hlt.le,h1.le⟩
    have hmem : t ∈ S := ⟨⟨hb.1.1.1.trans ht.1,ht.2⟩,he.le⟩
    have htb : t=b := le_antisymm (hb.2 hmem) ht.1
    rw [htb] at he
    exact hlt.ne he
  have hat : a < τ := lt_of_le_of_ne (ha.2 (show τ ∈ S from ⟨⟨hτ.1.le,hτ.2.le⟩,hvisit.le⟩)) (by
    intro he
    rw [he] at hfa
    exact hvisit.ne hfa)
  have htb : τ < b := lt_of_le_of_ne (hb.2 (show τ ∈ S from ⟨⟨hτ.1.le,hτ.2.le⟩,hvisit.le⟩)) (by
    intro he
    rw [← he] at hfb
    exact hvisit.ne hfb)
  exact ⟨a,b,ha0,hat,htb,hb1,hfa,hfb,fun t ht hf =>
    ⟨ha.2 ⟨ht,hf⟩,hb.2 ⟨ht,hf⟩⟩⟩

end Zarankiewicz

end

end OAI

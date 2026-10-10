import OAI.Combinatorics.Crossing.FirstLastVisits

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem last_sublevel_visit (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ)
    (h0 : f 0 < r) (h1 : r < f 1) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ f b=r ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ r → t ≤ b) := by
  let S : Set ℝ := Set.Icc 0 1 ∩ {t | f t ≤ r}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  obtain ⟨b,hb⟩ := hS.exists_isGreatest ⟨0,⟨by norm_num,by norm_num⟩,h0.le⟩
  have hb1 : b < 1 := lt_of_le_of_ne hb.1.1.2 (by
    intro he
    have hh := hb.1.2
    rw [he] at hh
    exact (not_le_of_gt h1) hh)
  have hfb : f b=r := by
    apply le_antisymm hb.1.2
    by_contra hn
    have hlt : f b < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hb.1.1.2 hf.continuousOn ⟨hlt.le,h1.le⟩
    have hmem : t ∈ S := ⟨⟨hb.1.1.1.trans ht.1,ht.2⟩,he.le⟩
    have htb : t=b := le_antisymm (hb.2 hmem) ht.1
    rw [htb] at he
    exact hlt.ne he
  have hb0 : 0 < b := lt_of_le_of_ne hb.1.1.1 (by
    intro he
    rw [← he] at hfb
    exact h0.ne hfb)
  exact ⟨b,hb0,hb1,hfb,fun t ht hh => hb.2 ⟨ht,hh⟩⟩

theorem first_sublevel_visit (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ)
    (h0 : r < f 0) (h1 : f 1 < r) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ f a=r ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ r → a ≤ t) := by
  obtain ⟨b,hb0,hb1,hfb,hb⟩ := last_sublevel_visit (fun t => f (1-t))
    (hf.comp (continuous_const.sub continuous_id)) r (by simpa using h1) (by simpa using h0)
  refine ⟨1-b,by linarith,by linarith,hfb,?_⟩
  intro t ht hh
  have he := hb (1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩ (by simpa using hh)
  linarith

end Zarankiewicz

end

end OAI

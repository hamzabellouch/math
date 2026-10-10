import OAI.Analysis.LipschitzHilbert.Trees.SourceThresholdSum

namespace OAI

/-! A finite collection has a dyadic level below all its positive
densities, and a level above any prescribed initial size or density. -/
noncomputable section
namespace LipschitzHilbert

theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (d : ι → ℝ) :
    ∃ delta : ℝ, 0<delta ∧ ∀ q∈S, 0<d q → delta≤d q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨delta,hdelta,hlower⟩ := ih
    by_cases hd : 0<d a
    · refine ⟨min delta (d a),lt_min hdelta hd,?_⟩
      intro q hq hqpos
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hlower q hq hqpos)
    · refine ⟨delta,hdelta,?_⟩
      intro q hq hqpos
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact (hd hqpos).elim
      · exact hlower q hq hqpos

theorem exists_dyadic_zero_detection {ι : Type*} (S : Finset ι) (d : ι → ℝ) :
    ∃ k : ℤ, ∀ q∈S, d q≤(2:ℝ)^k → d q≤0 := by
  obtain ⟨delta,hdelta,hlower⟩ := finite_positive_lower_bound S d
  obtain ⟨k,hk⟩ := exists_mem_Ioc_zpow hdelta (by norm_num : (1:ℝ)<2)
  refine ⟨k,?_⟩
  intro q hq hsmall
  by_contra hn
  have hpos : 0<d q := lt_of_not_ge hn
  exact (not_le_of_gt hk.1) (hsmall.trans' (hlower q hq hpos))

theorem exists_dyadic_upper_level (B : ℝ) : ∃ k : ℤ, B<(2:ℝ)^k := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1:ℝ)<2)
  exact ⟨n,by simpa only [zpow_natCast] using hn⟩

end LipschitzHilbert

end

end OAI

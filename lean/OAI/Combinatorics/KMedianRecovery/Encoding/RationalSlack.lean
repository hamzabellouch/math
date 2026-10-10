import Mathlib

namespace OAI

namespace MetricKMedianRecovery.ParameterBounds
open Filter

lemma exists_rational_slack (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∃ q : ℚ, 0 < q ∧ (q:ℝ) ≤ 1/12 ∧ (q:ℝ) ≤ c/1000 ∧
      (q:ℝ)^2 ≤ c/(6*(T+2)) := by
  have hb : 0 < c/(6*(T+2)) := by positivity
  have hm : 0 < min (1/12:ℝ) (min (c/1000) (Real.sqrt (c/(6*(T+2))))) :=
    lt_min (by norm_num) (lt_min (by positivity) (Real.sqrt_pos.2 hb))
  obtain ⟨q,hq0,hq⟩ := exists_rat_btwn hm
  have hqa := (lt_min_iff.mp hq).1
  have hqb := (lt_min_iff.mp (lt_min_iff.mp hq).2).1
  have hqc := (lt_min_iff.mp (lt_min_iff.mp hq).2).2
  refine ⟨q,by exact_mod_cast hq0,hqa.le,hqb.le,?_⟩
  nlinarith [Real.sq_sqrt hb.le]

lemma exists_size_threshold (c v : ℝ) (hc : 0 < c) (hv : 0 < v) :
    ∃ Nstar : ℕ, 1 ≤ Nstar ∧ ∀ N : ℕ, Nstar ≤ N →
      (N:ℝ)^2/(2:ℝ)^N ≤ v ∧ 2/(N:ℝ) ≤ c/200 := by
  have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ) < 2)).eventually
    (gt_mem_nhds hv)
  have h2 := (tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).eventually
    (gt_mem_nhds (by positivity : (0:ℝ) < c/200))
  obtain ⟨Nstar,hN⟩ := eventually_atTop.mp (h1.and h2)
  refine ⟨max 1 Nstar,le_max_left _ _,?_⟩
  intro N h
  exact ⟨(hN N ((le_max_right _ _).trans h)).1.le,
    (hN N ((le_max_right _ _).trans h)).2.le⟩

end MetricKMedianRecovery.ParameterBounds

end OAI

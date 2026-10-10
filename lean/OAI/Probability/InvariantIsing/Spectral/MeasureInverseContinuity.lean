import OAI.Probability.InvariantIsing.Spectral.MeasureResolvent

namespace OAI

/-! Order tests and continuity for the inverse across the capped branch. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

theorem measureInverse_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) (hb : e < b) :
    measureInverse μ e x ≤ b ↔ measureResolvent μ b ≤ x := by
  by_cases hex : ∃ r, e < r ∧ measureResolvent μ r = x
  · rw [measureInverse, dite_eq_left hex]
    have hs := hex.choose_spec
    constructor
    · intro hrb
      rcases hrb.eq_or_lt with h | h
      · rw [← h, hs.2]
      · have ht := measureResolvent_strictAnti μ hμ hs.1 h
        rw [hs.2] at ht
        exact ht.le
    · intro hR
      by_contra hnot
      have ht := measureResolvent_strictAnti μ hμ hb (lt_of_not_ge hnot)
      rw [hs.2] at ht
      exact (not_lt_of_ge hR) ht
  · rw [measureInverse, dite_eq_right hex]
    constructor
    · intro _
      by_contra hnot
      exact hex (exists_measureResolvent_solution μ hμ hb hx (lt_of_not_ge hnot).le)
    · intro _
      exact hb.le

theorem measureInverse_lt_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) (hb : e < b) :
    measureInverse μ e x < b ↔ measureResolvent μ b < x := by
  by_cases hex : ∃ r, e < r ∧ measureResolvent μ r = x
  · rw [measureInverse, dite_eq_left hex]
    have hs := hex.choose_spec
    constructor
    · intro hrb
      have ht := measureResolvent_strictAnti μ hμ hs.1 hrb
      rwa [hs.2] at ht
    · intro hR
      by_contra hnot
      rcases (le_of_not_gt hnot).eq_or_lt with h | h
      · rw [h, hs.2] at hR
        exact lt_irrefl _ hR
      · have ht := measureResolvent_strictAnti μ hμ hb h
        rw [hs.2] at ht
        exact (not_lt_of_ge ht.le) hR
  · rw [measureInverse, dite_eq_right hex]
    have hv : measureResolvent μ b < x := by
      by_contra hnot
      exact hex (exists_measureResolvent_solution μ hμ hb hx (le_of_not_gt hnot))
    exact ⟨fun _ => hv, fun _ => hb⟩

theorem continuousAt_measureInverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) :
    ContinuousAt (measureInverse μ e) x := by
  have hbound := (measureInverse_bounds μ hμ hx).1
  have hxp : ∀ᶠ y in 𝓝 x, 0 < y := Ioi_mem_nhds hx
  apply tendsto_order.2
  constructor
  · intro l hl
    by_cases hle : l < e
    · filter_upwards [hxp] with y hy
      exact hle.trans_le (measureInverse_bounds μ hμ hy).1
    · let c := (l + measureInverse μ e x) / 2
      have hec : e < c := by dsimp only [c]; linarith [le_of_not_gt hle]
      have hlc : l < c := by dsimp only [c]; linarith
      have hci : c < measureInverse μ e x := by dsimp only [c]; linarith
      have hR : x < measureResolvent μ c := by
        by_contra hnot
        exact (not_le_of_gt hci)
          ((measureInverse_le_iff μ hμ hx hec).mpr (le_of_not_gt hnot))
      filter_upwards [hxp, Iio_mem_nhds hR] with y hy hRy
      have hnot : ¬ measureInverse μ e y ≤ c := by
        intro hle
        exact (not_le_of_gt hRy) ((measureInverse_le_iff μ hμ hy hec).mp hle)
      exact hlc.trans (lt_of_not_ge hnot)
  · intro u hu
    have heu : e < u := hbound.trans_lt hu
    have hR := (measureInverse_lt_iff μ hμ hx heu).mp hu
    filter_upwards [hxp, Ioi_mem_nhds hR] with y hy hRy
    exact (measureInverse_lt_iff μ hμ hy heu).mpr hRy

theorem continuousAt_measureR_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) :
    ContinuousAt (measureR μ e) x := by
  have hc : ContinuousAt (fun y => measureInverse μ e y - 1 / y) x :=
    (continuousAt_measureInverse μ hμ hx).sub
    (continuousAt_const.div continuousAt_id hx.ne')
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [measureR, ite_eq_left (show 0 < y from hy)]

end InvariantIsing

end

end OAI

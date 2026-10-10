import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology unitInterval

namespace Problem356.Transport

/-- Every probability level strictly between zero and one is achieved by a continuous CDF. -/
theorem exists_cdf_eq_of_continuous (μ : Measure ℝ)
    (hc : Continuous (cdf μ)) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ x : ℝ, cdf μ x = u := by
  have h := isPreconnected_univ.intermediate_value_Ioo
    (l₁ := atBot) (l₂ := atTop) (by simp) (by simp) hc.continuousOn
    (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ) ⟨hu0, hu1⟩
  simpa only [image_univ, mem_range] using h

/-- The probability integral transform, expressed on CDF sublevel sets. -/
theorem measureReal_cdf_sublevel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    μ.real {x : ℝ | cdf μ x ≤ u} = u := by
  let s : Set ℝ := {x | cdf μ x ≤ u}
  have hs0 : 0 ≤ μ.real s := measureReal_nonneg
  have hs1 : μ.real s ≤ 1 := measureReal_le_one
  apply le_antisymm
  · by_contra! h
    obtain ⟨v, huv, hvs⟩ := exists_between h
    obtain ⟨x, hx⟩ := exists_cdf_eq_of_continuous μ hc (hu0.trans_lt huv) (hvs.trans_le hs1)
    have hsub : s ⊆ Iic x := by
      intro y hy
      change y ≤ x
      by_contra! hxy
      have hmon := monotone_cdf μ hxy.le
      have hy' : cdf μ y ≤ u := hy
      rw [hx] at hmon
      linarith
    have hle := measureReal_mono (μ := μ) hsub
    rw [← cdf_eq_real μ x, hx] at hle
    linarith
  · by_contra! h
    obtain ⟨v, hsv, hvu⟩ := exists_between h
    obtain ⟨x, hx⟩ := exists_cdf_eq_of_continuous μ hc (hs0.trans_lt hsv) (hvu.trans_le hu1)
    have hsub : Iic x ⊆ s := by
      intro y hy
      have hmon := monotone_cdf μ hy
      change cdf μ y ≤ u
      rw [hx] at hmon
      exact hmon.trans hvu.le
    have hle := measureReal_mono (μ := μ) hsub
    rw [← cdf_eq_real μ x, hx] at hle
    linarith

/-- A continuous CDF sends its law to uniform probability on the unit interval. -/
theorem map_cdf_unitInterval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) :
    μ.map (fun x : ℝ => (⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩ : I)) = volume := by
  let f : ℝ → I := fun x => ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩
  have hf : Measurable f := hc.measurable.subtype_mk
  apply Measure.ext_of_Iic
  intro u
  rw [Measure.map_apply hf measurableSet_Iic, unitInterval.volume_Iic]
  change μ {x : ℝ | cdf μ x ≤ (u : ℝ)} = ENNReal.ofReal (u : ℝ)
  rw [← ofReal_measureReal (measure_ne_top μ _),
    measureReal_cdf_sublevel μ hc u.property.1 u.property.2]

end Problem356.Transport

end

end OAI

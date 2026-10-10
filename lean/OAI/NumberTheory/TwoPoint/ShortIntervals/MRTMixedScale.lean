import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedThreshold

namespace OAI

/-! Explicit sufficient logarithmic scale separations for the amplified
moment. The factorial budget is derived, rather than assumed. -/

namespace TwoPointCorrelations

lemma mrt_amplification_cost_coarse {Y u a : ℝ}
    (hY0 : 0 < Y) (hu0 : 0 < u) (hY : 1 ≤ Real.log Y)
    (hYu : Real.log Y ≤ Real.log u) (ha : a ≤ 1 / 4) :
    mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y) a ≤
      8 * (Real.log u / Real.log Y) * (Real.log (Real.log u) + 1) +
        2 * Real.log Y := by
  have hu : 1 ≤ Real.log u := hY.trans hYu
  have hx0 : 0 ≤ Real.log u := by linarith
  have hy0 : 0 < Real.log Y := by linarith
  have hq : 1 ≤ Real.log u / Real.log Y := (le_div_iff₀ hy0).mpr (by simpa using hYu)
  have hl : 1 ≤ Real.log (Real.log u) + 1 := by
    linarith [Real.log_nonneg hu]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := mul_le_mul_of_nonneg_left hlog1
    (show 0 ≤ Real.log u / Real.log Y + 2 by positivity)
  have hql := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ Real.log u / Real.log Y by positivity)
  have hq1 := mul_le_mul_of_nonneg_right hq
    (show 0 ≤ Real.log (Real.log u) + 1 by positivity)
  have hay := mul_le_mul_of_nonneg_right ha hy0.le
  have hc := mrt_amplification_cost_bound hY hu hY0 hu0 (a := a)
  nlinarith

lemma mrt_mixed_scale_guard {η x y d : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hd : 0 < d)
    (hsep : 32 * d * (Real.log x + 1) ≤ η * y)
    (hsize : 8 * d * y ≤ η * x) :
    8 * (x / y) * (Real.log x + 1) + 2 * y ≤ η * x / (2 * d) := by
  have hh := mul_le_mul_of_nonneg_left hsep (div_nonneg hx hy.le)
  have he : x / y * (η * y) = η * x := by field_simp
  rw [he] at hh
  apply (le_div_iff₀ (by positivity : 0 < 2 * d)).mpr
  nlinarith

theorem mrt_amplification_cost_of_separation {η Y u : ℝ}
    (hη : 0 ≤ η) (j : ℕ) (hY0 : 0 < Y) (hu0 : 0 < u)
    (hY : 1 ≤ Real.log Y) (hYu : Real.log Y ≤ Real.log u)
    (hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y)
    (hsize : 8 * ((j : ℝ) + 2) ^ 2 * Real.log Y ≤ η * Real.log u) :
    mrtAmplificationCost (mrtAmplificationOrder Y u) (Real.log Y)
        (mrtFrequencyExponent η j) ≤
      η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2) := by
  apply (mrt_amplification_cost_coarse hY0 hu0 hY hYu
    (show mrtFrequencyExponent η j ≤ 1 / 4 by
      have hh := (mrtFrequencyExponent_bounds hη j).2
      linarith)).trans
  exact mrt_mixed_scale_guard (by linarith : 0 ≤ Real.log u)
    (by linarith : 0 < Real.log Y) (by positivity) hsep hsize

theorem mrt_mixed_threshold_of_separation {η Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hY0 : 0 < Y) (hu0 : 0 < u) (hY : 1 ≤ Real.log Y)
    (hYu : Real.log Y ≤ Real.log u) (hτ : 0 ≤ τ)
    (hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y)
    (hsize : 8 * ((j : ℝ) + 2) ^ 2 * Real.log Y ≤ η * Real.log u) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder Y u + 1) * Y) *
        ((mrtAmplificationOrder Y u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder Y u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  exact mrt_mixed_threshold_amplification hη hη'
    ((Real.log_pos_iff hY0.le).mp (by linarith))
    ((Real.log_nonneg_iff hu0).mp (by linarith)) hτ j
    (mrt_amplification_cost_of_separation hη j hY0 hu0 hY hYu hsep hsize)

end TwoPointCorrelations

end OAI

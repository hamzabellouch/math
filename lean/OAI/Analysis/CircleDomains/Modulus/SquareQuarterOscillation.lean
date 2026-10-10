import OAI.Analysis.CircleDomains.Sobolev.SquareAverageComparison

namespace OAI

/-! Pointwise control by the mean oscillations on quarter-scale squares.
The geometric decay is matched to square-integrable energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma squareAverage_quartering {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    |squareAverage f c r-squareAverage f c (r/4)| ≤
      16*(⨍ p in coordinateSquare c r, |f p-squareAverage f c r|) := by
  rw [abs_sub_comm]
  apply abs_average_sub_average_le_oscillation
    (closedBall_subset_closedBall (by linarith))
    (coordinateSquare_volume_ne_zero c (by positivity))
    (coordinateSquare_compact c r).measure_lt_top.ne
    (hf.continuousOn.integrableOn_compact (coordinateSquare_compact c r))
  change volume.real (coordinateSquare c r) ≤ 16*volume.real (coordinateSquare c (r/4))
  rw [coordinateSquare_real_volume c hr.le,
    coordinateSquare_real_volume c (show 0 ≤ r/4 by positivity)]
  nlinarith

lemma square_point_average_bound_quarters {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r K : ℝ} (hr : 0 < r)
    (hosc : ∀ n : ℕ, (⨍ p in coordinateSquare c (r*(1/4:ℝ)^n),
      |f p-squareAverage f c (r*(1/4:ℝ)^n)|) ≤ K*(1/2:ℝ)^n) :
    |f c-squareAverage f c r| ≤ 32*K := by
  have hpos (n : ℕ) : 0 < r*(1/4:ℝ)^n := mul_pos hr (pow_pos (by norm_num) n)
  have hlim : Tendsto (fun n : ℕ => r*(1/4:ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
        (by norm_num : (1/4:ℝ) < 1)).const_mul r
  have hstep (n : ℕ) : dist (squareAverage f c (r*(1/4:ℝ)^n))
      (squareAverage f c (r*(1/4:ℝ)^(n+1))) ≤ (16*K)*(1/2:ℝ)^n := by
    have he : r*(1/4:ℝ)^(n+1) = (r*(1/4:ℝ)^n)/4 := by rw [pow_succ]; ring
    rw [he, Real.dist_eq]
    calc
      _ ≤ 16*(⨍ p in coordinateSquare c (r*(1/4:ℝ)^n),
          |f p-squareAverage f c (r*(1/4:ℝ)^n)|) := squareAverage_quartering hf c (hpos n)
      _ ≤ 16*(K*(1/2:ℝ)^n) := mul_le_mul_of_nonneg_left (hosc n) (by norm_num)
      _ = _ := by ring
  have hb := dist_le_of_le_geometric_of_tendsto₀ (1/2:ℝ) (16*K) (by norm_num)
    hstep (squareAverage_tendsto hf c hpos hlim)
  simpa only [pow_zero, mul_one, Real.dist_eq, abs_sub_comm] using
    (show dist (squareAverage f c (r*(1/4:ℝ)^0)) (f c) ≤ 32*K by
      convert hb using 1
      ring)

end CircleDomainRigidity

end

end OAI

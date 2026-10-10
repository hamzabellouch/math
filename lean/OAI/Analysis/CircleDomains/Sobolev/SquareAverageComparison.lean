import OAI.Analysis.CircleDomains.Uniformization.SquareAverageLimit
import OAI.Analysis.CircleDomains.Sobolev.AverageSubsets

namespace OAI

/-! Quantitative comparison of averages on nested comparable coordinate squares. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma squareAverage_comparison {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {c d : ℝ × ℝ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hsub : coordinateSquare c r ⊆ coordinateSquare d R) (hscale : R ≤ 2*r) :
    |squareAverage f c r-squareAverage f d R| ≤
    4*(⨍ p in coordinateSquare d R, |f p-squareAverage f d R|) := by
  apply abs_average_sub_average_le_oscillation hsub
    (coordinateSquare_volume_ne_zero c hr) (coordinateSquare_compact d R).measure_lt_top.ne
    (hf.continuousOn.integrableOn_compact (coordinateSquare_compact d R))
  rw [coordinateSquare_real_volume d hR.le, coordinateSquare_real_volume c hr.le]
  nlinarith [mul_self_le_mul_self hR.le hscale]

lemma squareAverage_halving {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    |squareAverage f c r-squareAverage f c (r/2)| ≤
    4*(⨍ p in coordinateSquare c r, |f p-squareAverage f c r|) := by
  rw [abs_sub_comm]
  exact squareAverage_comparison hf (half_pos hr) hr
    (closedBall_subset_closedBall (by linarith)) (by linarith)

lemma square_point_average_bound {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (c : ℝ × ℝ) {r K : ℝ} (hr : 0 < r)
    (hosc : ∀ n : ℕ, (⨍ p in coordinateSquare c (r*(1/2:ℝ)^n),
      |f p-squareAverage f c (r*(1/2:ℝ)^n)|) ≤ K*(r*(1/2:ℝ)^n)) :
    |f c-squareAverage f c r| ≤ 8*K*r := by
  have hpos (n : ℕ) : 0 < r*(1/2:ℝ)^n := mul_pos hr (pow_pos (by norm_num) n)
  have hlim : Tendsto (fun n : ℕ => r*(1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).const_mul r
  have hstep (n : ℕ) : dist (squareAverage f c (r*(1/2:ℝ)^n))
      (squareAverage f c (r*(1/2:ℝ)^(n+1))) ≤ (4*K*r)*(1/2:ℝ)^n := by
    have he : r*(1/2:ℝ)^(n+1) = (r*(1/2:ℝ)^n)/2 := by rw [pow_succ]; ring
    rw [he, Real.dist_eq]
    calc
      _ ≤ 4*(⨍ p in coordinateSquare c (r*(1/2:ℝ)^n),
          |f p-squareAverage f c (r*(1/2:ℝ)^n)|) := squareAverage_halving hf c (hpos n)
      _ ≤ 4*(K*(r*(1/2:ℝ)^n)) := mul_le_mul_of_nonneg_left (hosc n) (by norm_num)
      _ = _ := by ring
  have hb := dist_le_of_le_geometric_of_tendsto₀ (1/2:ℝ) (4*K*r) (by norm_num)
    hstep (squareAverage_tendsto hf c hpos hlim)
  simpa only [pow_zero, mul_one, Real.dist_eq, abs_sub_comm] using
    (show dist (squareAverage f c (r*(1/2:ℝ)^0)) (f c) ≤ 8*K*r by
      convert hb using 1
      ring)

end CircleDomainRigidity

end

end OAI

import OAI.Geometry.Relativity.CKS.ConstructedOuterMetric

namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma primitive_add {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    primitive a q r = primitive a q b + primitive b q r := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (positive_interval_integrable hq ha hb) (positive_interval_integrable hq hb hr)).symm

lemma heatDensity_tail {R r : ℝ} (hR : 12 ≤ R) (hr : 2*R^2 ≤ r) :
    heatDensity R r = 1/(2*r) := by
  have hRp : 0 < R := by linarith
  have hz : 5 ≤ r/R := (le_div_iff₀ hRp).mpr (by nlinarith)
  simp [heatDensity,bendingV_tail hRp hr,bendingZeta,zeta_one hz]

lemma heatTime_tail {R r : ℝ} (hR : 12 ≤ R) (hr : 2*R^2 ≤ r) :
    heatTime R r = heatTime R (2*R^2) + (Real.log r - Real.log (2*R^2))/2 := by
  have hRp : 0 < R := by linarith
  have ha : 0 < 2*R^2 := by positivity
  have hrp := ha.trans_le hr
  change primitive (3*R) (heatDensity R) r = _
  rw [primitive_add (heatDensity_smooth hRp).continuousOn (by positivity) ha hrp]
  congr 1
  have he : primitive (2*R^2) (heatDensity R) r = primitive (2*R^2) (fun s => 1/(2*s)) r := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact heatDensity_tail hR ((uIcc_of_le hr ▸ hs).1)
  rw [he]
  have hh : primitive (2*R^2) (fun s : ℝ => 1/(2*s)) r =
      Real.log r / 2 - Real.log (2*R^2)/2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s hs
      convert! (Real.hasDerivAt_log (ne_of_gt (positive_uIcc ha hrp hs))).div_const 2 using 1
      ring
    · apply positive_interval_integrable _ ha hrp
      exact (continuousOn_const.div (continuousOn_const.mul continuousOn_id)
        (fun s hs => ne_of_gt (mul_pos (by norm_num) hs)))
  rw [hh]
  ring

lemma paddingMass_tail {R r : ℝ} (hR : 0 < R) (hr : 2*R ≤ r) :
    paddingMass R r = paddingMass R (2*R) + 2/Real.sqrt (2*R) - 2/Real.sqrt r := by
  have ha : 0 < 2*R := by positivity
  have hrp := ha.trans_le hr
  change primitive R (fun s => paddingWeight R s * paddingDensity s) r = _
  rw [primitive_add (paddingIntegrand_smooth R).continuousOn hR ha hrp]
  have he : primitive (2*R) (fun s => paddingWeight R s * paddingDensity s) r =
      primitive (2*R) paddingDensity r := by
    apply intervalIntegral.integral_congr
    intro s hs
    change paddingWeight R s * paddingDensity s = paddingDensity s
    rw [paddingWeight_one hR ((uIcc_of_le hr ▸ hs).1),one_mul]
  rw [he,paddingDensity_integral ha hrp]
  change paddingMass R (2*R) + _ = _
  ring

def paddingCharge (R : ℝ) : ℝ := paddingMass R (2*R) + 2/Real.sqrt (2*R)

lemma paddingCharge_limit {R : ℝ} (hR : 0 < R) :
    Tendsto (paddingMass R) atTop (𝓝 (paddingCharge R)) := by
  have hs : Tendsto (fun r : ℝ => 2/Real.sqrt r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hh : Tendsto (fun r : ℝ => paddingCharge R - 2/Real.sqrt r) atTop (𝓝 (paddingCharge R)) := by
    simpa using (tendsto_const_nhds (x := paddingCharge R)).sub hs
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2*R)] with r hr
  symm
  simpa [paddingCharge] using paddingMass_tail hR hr

lemma paddingCharge_bounds {R : ℝ} (hR : 0 < R) :
    0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R := by
  have hh := paddingCharge_limit hR
  constructor
  · apply ge_of_tendsto hh
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact paddingMass_nonneg hR hr
  · apply le_of_tendsto hh
    filter_upwards [eventually_ge_atTop R] with r hr
    exact paddingMass_bound hR hr

end
end CKSBending

end

end OAI

import OAI.MeasureTheory.Falconer.Angular.StationaryChartCutoffs

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

noncomputable def stationaryCosineChart (θ : ℝ) : ℝ := 2*Real.cos (θ/2)
noncomputable def circleStationaryResidual (θ : ℝ) : ℝ :=
  1-stationaryCutoff (stationarySineChart θ)-stationaryCutoff (stationaryCosineChart θ)

 theorem stationary_charts_sq (θ : ℝ) :
    stationarySineChart θ^2 + stationaryCosineChart θ^2 = 4 := by
  have h := Real.sin_sq_add_cos_sq (θ/2)
  unfold stationarySineChart stationaryCosineChart
  nlinarith

 theorem stationary_charts_product (θ : ℝ) :
    stationarySineChart θ * stationaryCosineChart θ = 2*Real.sin θ := by
  have h := Real.sin_two_mul (θ/2)
  rw [show 2*(θ/2)=θ by ring] at h
  unfold stationarySineChart stationaryCosineChart
  nlinarith

 theorem stationaryCutoff_one_of_abs_le {u : ℝ} (hu : |u| ≤ 1/2) : stationaryCutoff u = 1 := by
  exact stationaryCutoff.one_of_mem_closedBall (by simpa [stationaryCutoff,Real.dist_eq] using hu)

 theorem stationaryCutoff_zero_of_abs_le {u : ℝ} (hu : 1 ≤ |u|) : stationaryCutoff u = 0 := by
  exact stationaryCutoff.zero_of_le_dist (by simpa [stationaryCutoff,Real.dist_eq] using hu)

 theorem circleStationaryResidual_zero_sine {θ : ℝ} (hθ : |stationarySineChart θ| ≤ 1/2) :
    circleStationaryResidual θ = 0 := by
  have h := stationary_charts_sq θ
  have hv : 1 ≤ |stationaryCosineChart θ| := by
    nlinarith [sq_abs (stationarySineChart θ),sq_abs (stationaryCosineChart θ),
      abs_nonneg (stationarySineChart θ),abs_nonneg (stationaryCosineChart θ)]
  simp [circleStationaryResidual,stationaryCutoff_one_of_abs_le hθ,stationaryCutoff_zero_of_abs_le hv]

 theorem circleStationaryResidual_zero_cosine {θ : ℝ} (hθ : |stationaryCosineChart θ| ≤ 1/2) :
    circleStationaryResidual θ = 0 := by
  have h := stationary_charts_sq θ
  have hv : 1 ≤ |stationarySineChart θ| := by
    nlinarith [sq_abs (stationarySineChart θ),sq_abs (stationaryCosineChart θ),
      abs_nonneg (stationarySineChart θ),abs_nonneg (stationaryCosineChart θ)]
  simp [circleStationaryResidual,stationaryCutoff_one_of_abs_le hθ,stationaryCutoff_zero_of_abs_le hv]

 theorem circleStationaryResidual_support :
    tsupport circleStationaryResidual ⊆ {θ : ℝ | (1:ℝ)/8 ≤ |Real.sin θ|} := by
  apply closure_minimal
  · intro θ hθ
    have hu : 1/2 < |stationarySineChart θ| := lt_of_not_ge (fun hh => hθ (circleStationaryResidual_zero_sine hh))
    have hv : 1/2 < |stationaryCosineChart θ| := lt_of_not_ge (fun hh => hθ (circleStationaryResidual_zero_cosine hh))
    have he := congrArg abs (stationary_charts_product θ)
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at he
    dsimp
    nlinarith [mul_pos (sub_pos.mpr hu) (sub_pos.mpr hv)]
  · exact isClosed_le continuous_const Real.continuous_sin.abs

 theorem circleStationaryResidual_contDiff : ContDiff ℝ ∞ circleStationaryResidual := by
  have hs : ContDiff ℝ ∞ stationarySineChart := by unfold stationarySineChart; fun_prop
  have hc : ContDiff ℝ ∞ stationaryCosineChart := by unfold stationaryCosineChart; fun_prop
  exact (contDiff_const.sub (stationaryCutoff.contDiff.comp hs)).sub (stationaryCutoff.contDiff.comp hc)

 theorem circleStationaryResidual_eventually_zero {θ : ℝ} (hθ : Real.cos (θ/2) = 0) :
    circleStationaryResidual =ᶠ[𝓝 θ] (fun _ => 0) := by
  have hc : Continuous stationaryCosineChart := by unfold stationaryCosineChart; fun_prop
  have he : stationaryCosineChart θ = 0 := by simp [stationaryCosineChart,hθ]
  have hn : ∀ᶠ x in 𝓝 θ, |stationaryCosineChart x| < 1/2 := by
    exact hc.abs.continuousAt.eventually (gt_mem_nhds (by simp [he]))
  filter_upwards [hn] with x hx
  exact circleStationaryResidual_zero_cosine hx.le

end PlanarFalconer

end OAI

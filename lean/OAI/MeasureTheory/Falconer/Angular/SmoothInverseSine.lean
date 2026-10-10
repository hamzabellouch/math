import OAI.MeasureTheory.Falconer.Angular.StationaryChartCutoffs

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

noncomputable def sineZeroCutoff (η : ℝ) (hη : 0 < η) : ContDiffBump (0:ℝ) :=
  ⟨η/2,η,half_pos hη,half_lt_self hη⟩
noncomputable def smoothInverseSine (η : ℝ) (hη : 0 < η) (θ : ℝ) : ℝ :=
  (1-sineZeroCutoff η hη (Real.sin θ))*(Real.sin θ)⁻¹

 theorem smoothInverseSine_contDiff (η : ℝ) (hη : 0 < η) :
    ContDiff ℝ ∞ (smoothInverseSine η hη) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : Real.sin x = 0
  · have hb : (sineZeroCutoff η hη : ℝ → ℝ) =ᶠ[𝓝 (Real.sin x)] (fun _ => 1) := by
      rw [hx]
      exact (sineZeroCutoff η hη).eventuallyEq_one
    have he : smoothInverseSine η hη =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hb.comp_tendsto Real.continuous_sin.continuousAt] with y hy
      simp only [Function.comp_apply] at hy
      simp [smoothInverseSine,hy]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hb : ContDiffAt ℝ ∞ (fun y => sineZeroCutoff η hη (Real.sin y)) x :=
      (sineZeroCutoff η hη).contDiffAt.comp x Real.contDiff_sin.contDiffAt
    exact (contDiffAt_const.sub hb).mul (Real.contDiff_sin.contDiffAt.inv hx)

 theorem smoothInverseSine_eq {η : ℝ} (hη : 0 < η) {θ : ℝ}
    (hθ : η ≤ |Real.sin θ|) : (Real.sin θ)*smoothInverseSine η hη θ = 1 := by
  have hb : sineZeroCutoff η hη (Real.sin θ) = 0 :=
    (sineZeroCutoff η hη).zero_of_le_dist (by simpa [sineZeroCutoff,Real.dist_eq] using hθ)
  have hs : Real.sin θ ≠ 0 := by intro he; simp [he] at hθ; linarith
  simp [smoothInverseSine,hb,hs]

end PlanarFalconer

end OAI

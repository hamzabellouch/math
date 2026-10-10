import OAI.Geometry.Perimeter.Regularity.GeoComposition

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def minimalFlux (z : Euc n) : Euc n := (Real.sqrt (1+‖z‖^2))⁻¹ • z

theorem minimalFlux_scalar_smooth : ContDiff ℝ ∞ (fun z : Euc n ↦ (Real.sqrt (1+‖z‖^2))⁻¹) := by
  apply ContDiff.inv
  · exact (contDiff_const.add (contDiff_id.norm_sq ℝ)).sqrt (fun z ↦ by positivity)
  · intro z; positivity

theorem minimalFlux_smooth : ContDiff ℝ ∞ (minimalFlux (n:=n)) :=
  minimalFlux_scalar_smooth.smul contDiff_id

theorem minimalFlux_fderiv_zero : fderiv ℝ (minimalFlux (n:=n)) 0 = ContinuousLinearMap.id ℝ (Euc n) := by
  unfold minimalFlux
  have hc : DifferentiableAt ℝ (fun z : Euc n ↦ (Real.sqrt (1+‖z‖^2))⁻¹) 0 :=
    (minimalFlux_scalar_smooth.differentiable (by simp)).differentiableAt
  have he := fderiv_fun_smul hc
    (differentiableAt_id : DifferentiableAt ℝ (fun z : Euc n ↦ z) 0)
  convert he using 1 <;> simp

theorem minimalFlux_exists_small {δ : ℝ} (hδ : 0<δ) : ∃ ε : ℝ, 0<ε ∧
    ∀ z : Euc n, ‖z‖<ε → ‖ContinuousLinearMap.id ℝ (Euc n)-fderiv ℝ minimalFlux z‖< min δ (1/2) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (minimalFlux (n:=n))) :=
    minimalFlux_smooth.fderiv_right (by simp)
  have hc : ContinuousAt (fderiv ℝ (minimalFlux (n:=n))) 0 := hD.continuous.continuousAt
  obtain ⟨ε,hε,hh⟩ := Metric.continuousAt_iff.mp hc (min δ (1/2)) (lt_min hδ (by norm_num))
  refine ⟨ε,hε,fun z hz ↦ ?_⟩
  have hv := hh (by simpa only [dist_zero_right] using hz)
  rwa [minimalFlux_fderiv_zero,dist_eq_norm,norm_sub_rev] at hv

end RPISingularHarnack

end

end OAI

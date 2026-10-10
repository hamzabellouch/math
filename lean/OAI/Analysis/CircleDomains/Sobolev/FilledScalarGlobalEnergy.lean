import OAI.Analysis.CircleDomains.Sobolev.FilledScalarEnergy

namespace OAI

/-! The finite holes contribute no ordinary gradient energy. Their circular
boundaries are null, including degenerate point circles. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace HoleFilling
variable {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

 theorem filled_fderiv_on_ball (s : (R.model.stages n).indices) {z : ℂ}
    (hz : z ∈ ball (F.center s) (F.radius s)) : fderiv ℝ F.filled z = 0 := by
  have he : F.filled =ᶠ[𝓝 z] fun _ => clipScalar (F.value s) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact F.filled_on_hole s (ball_subset_closedBall hw)
  rw [he.fderiv_eq, fderiv_const_apply]

 theorem filled_energy_eq_indicator_ae :
    euclideanGradientEnergy F.filled =ᵐ[volume]
      (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain).indicator
        (euclideanGradientEnergy F.filled) := by
  classical
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  have hs : ∀ᵐ z ∂(volume : Measure ℂ), ∀ s, z ∉ sphere (F.center s) (F.radius s) := by
    apply ae_all_iff.mpr
    intro s
    exact compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (F.center s) (F.radius s))
  filter_upwards [hs] with z hz
  by_cases hU : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain
  · rw [indicator_of_mem hU]
  · rw [indicator_of_notMem hU]
    have hout : z ∈ ⋃ s, closedBall (F.center s) (F.radius s) := by
      rw [F.complement] at hU
      exact not_not.mp hU
    obtain ⟨s, hsz⟩ := mem_iUnion.mp hout
    have hball : z ∈ ball (F.center s) (F.radius s) :=
      lt_of_le_of_ne hsz (fun he => hz s he)
    simp only [euclideanGradientEnergy, F.filled_fderiv_on_ball s hball, zero_apply,
      zero_pow (by decide : 2 ≠ 0), zero_add]

 theorem filled_energy_integrable_iff :
    Integrable (euclideanGradientEnergy F.filled) ↔
      IntegrableOn (euclideanGradientEnergy F.filled)
        (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  rw [← integrable_indicator_iff hU.measurableSet]
  exact integrable_congr F.filled_energy_eq_indicator_ae

 theorem integral_filled_energy :
    (∫ z, euclideanGradientEnergy F.filled z) =
      ∫ z in (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain),
        euclideanGradientEnergy F.filled z := by
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  rw [integral_congr_ae F.filled_energy_eq_indicator_ae, integral_indicator hU.measurableSet]

end HoleFilling

 theorem eventually_filled_global_energy (R : RetainedRealCircleModel d π Q) (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      Integrable (euclideanGradientEnergy F.filled) ∧
      (∫ z, euclideanGradientEnergy F.filled z) <
      (∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + modelError n := by
  filter_upwards [R.eventually_filled_energy i] with n hn F
  rw [F.filled_energy_integrable_iff, F.integral_filled_energy]
  exact hn F

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI

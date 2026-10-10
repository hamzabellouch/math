import OAI.Analysis.CircleDomains.Sobolev.ClippedScalarEnergy

namespace OAI

/-! L² bounds for the clipped filled functions' differentials, extended by
zero inside the actual target holes. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem eventually_filled_energy (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      IntegrableOn (euclideanGradientEnergy F.filled)
        (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) ∧
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain),
        euclideanGradientEnergy F.filled z) <
      (∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + modelError n := by
  filter_upwards [R.eventually_energy i] with n hn F
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  have hm : Measurable (euclideanGradientEnergy F.filled) :=
    ((measurable_fderiv_apply_const ℝ F.filled (1 : ℂ)).pow_const 2).add
      ((measurable_fderiv_apply_const ℝ F.filled Complex.I).pow_const 2)
  have hle : ∀ᵐ z ∂volume.restrict (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain),
      euclideanGradientEnergy F.filled z ≤ euclideanGradientEnergy (R.transferred i n) z := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact F.filled_gradient_le hz
  have hi : IntegrableOn (euclideanGradientEnergy F.filled)
      (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
    apply hn.1.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanGradientEnergy_nonneg _ _)] using hz
  exact ⟨hi, (integral_mono_ae hi hn.1 hle).trans_lt hn.2⟩

 theorem eventually_filled_tail_energy (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      (∫ z in R.targetTail n, euclideanGradientEnergy F.filled z) ≤
        ∫ z in R.targetTail n, euclideanGradientEnergy (R.transferred i n) z := by
  filter_upwards [R.eventually_energy i] with n hn F
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  have hm : Measurable (euclideanGradientEnergy F.filled) :=
    ((measurable_fderiv_apply_const ℝ F.filled (1 : ℂ)).pow_const 2).add
      ((measurable_fderiv_apply_const ℝ F.filled Complex.I).pow_const 2)
  have hle : ∀ᵐ z ∂volume.restrict (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain),
      euclideanGradientEnergy F.filled z ≤ euclideanGradientEnergy (R.transferred i n) z := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact F.filled_gradient_le hz
  have hi : IntegrableOn (euclideanGradientEnergy F.filled)
      (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
    apply hn.1.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanGradientEnergy_nonneg _ _)] using hz
  exact integral_mono_ae (hi.mono_set sdiff_subset) (hn.1.mono_set sdiff_subset)
    (ae_restrict_of_ae_restrict_of_subset sdiff_subset hle)

 theorem filled_tail_energy_tendsto (i : Fin m) (F : ∀ n, R.HoleFilling i n) :
    Tendsto (fun n => ∫ z in R.targetTail n, euclideanGradientEnergy (F n).filled z)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg
    (fun z => euclideanGradientEnergy_nonneg _ z))
    ((R.eventually_filled_tail_energy i).mono fun n hn => hn (F n)) (R.tail_energy_tendsto i)

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Sobolev.ScalarEnergyMeasure
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevNullLevels

namespace OAI

/-! Small open neighborhoods of countably many values for the actual
finite-energy scalar on an arbitrary open source domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_scalar_energy_nullSingleton
    (hcoarea : PlanarSobolevCoarea)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U) :
    NullSingletonClass (scalarEnergyMeasure U u W.weakGrad) := by
  constructor
  intro t
  rw [scalarEnergyMeasure, Measure.map_apply hu.measurable (measurableSet_singleton t),
    withDensity_apply _ (hu.measurable (measurableSet_singleton t)),
    Measure.restrict_restrict (hu.measurable (measurableSet_singleton t))]
  apply lintegral_eq_zero_of_ae_eq_zero
  have hz := local_sobolev_gradient_zero_on_null_values hcoarea hU hu W
    (measurableSet_singleton t) (measure_singleton t)
  rw [inter_comm] at hz
  filter_upwards [hz] with p hp
  simp only [hp, norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, Pi.zero_apply]

 theorem exists_small_open_local_energy_cover
    (hcoarea : PlanarSobolevCoarea)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {C : Set ℝ} (hC : C.Countable) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ O : Set ℝ, C ⊆ O ∧ IsOpen O ∧ volume O < ε ∧
      scalarEnergyMeasure U u W.weakGrad O < ε := by
  let μ := scalarEnergyMeasure U u W.weakGrad
  let : IsFiniteMeasure μ := scalarEnergyMeasure_finite (memLp_piLp_iff.mpr W.weakGrad_component_memLp)
  let : NullSingletonClass μ := local_scalar_energy_nullSingleton hcoarea hU hu W
  exact exists_small_open_energy_cover μ hC hε

end CircleDomainRigidity

end

end OAI

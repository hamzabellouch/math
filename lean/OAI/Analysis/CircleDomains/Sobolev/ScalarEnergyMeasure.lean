import OAI.Analysis.CircleDomains.Sobolev.SobolevNullLevels
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-! The pushforward of scalar Dirichlet energy has no atoms. This is
applied on the whole support of an old test, or on the fixed bounded
region used for the height. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def scalarEnergyMeasure (E : Set EuclideanPlane) (v : EuclideanPlane → ℝ)
    (V : EuclideanPlane → EuclideanPlane) : Measure ℝ :=
  Measure.map v ((volume.restrict E).withDensity (fun p => ENNReal.ofReal (‖V p‖^2)))

 theorem scalarEnergyMeasure_finite
    {E : Set EuclideanPlane} {v : EuclideanPlane → ℝ} {V : EuclideanPlane → EuclideanPlane}
    (hV : MemLp V 2 (volume.restrict E)) : IsFiniteMeasure (scalarEnergyMeasure E v V) := by
  have hi := hV.norm.integrable_sq
  have hfin : (∫⁻ p in E, ENNReal.ofReal (‖V p‖^2)) < ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal_abs,
      abs_sq] using hi.hasFiniteIntegral
  let := isFiniteMeasure_withDensity hfin.ne
  exact Measure.isFiniteMeasure_map _ _

 theorem scalarEnergyMeasure_nullSingleton
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E) :
    NullSingletonClass (scalarEnergyMeasure E v V) := by
  constructor
  intro t
  rw [scalarEnergyMeasure, Measure.map_apply hv.measurable (measurableSet_singleton t),
    withDensity_apply _ (hv.measurable (measurableSet_singleton t)),
    Measure.restrict_restrict (hv.measurable (measurableSet_singleton t))]
  apply lintegral_eq_zero_of_ae_eq_zero
  have hz := sobolev_gradient_zero_on_level hcoarea hv hw hLp hE hb t
  rw [inter_comm] at hz
  filter_upwards [hz] with p hp
  simp only [hp, norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, Pi.zero_apply]

 theorem exists_small_open_energy_cover
    (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {C : Set ℝ} (hC : C.Countable) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ O : Set ℝ, C ⊆ O ∧ IsOpen O ∧ volume O < ε ∧ μ O < ε := by
  obtain ⟨U, hCU, hU, hμU⟩ :=
    C.exists_isOpen_lt_of_lt (μ := μ) ε (by rw [hC.measure_zero μ]; exact hε)
  obtain ⟨V, hCV, hV, hvolV⟩ :=
    C.exists_isOpen_lt_of_lt (μ := volume) ε (by rw [hC.measure_zero volume]; exact hε)
  exact ⟨U ∩ V, subset_inter hCU hCV, hU.inter hV,
    (measure_mono inter_subset_right).trans_lt hvolV,
    (measure_mono inter_subset_left).trans_lt hμU⟩

end CircleDomainRigidity

end

end OAI

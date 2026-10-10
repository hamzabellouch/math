import OAI.Analysis.CircleDomains.Uniformization.ScalarLimitWitness
import OAI.Analysis.CircleDomains.Sobolev.BoundedWeakRange

namespace OAI

/-! The scalar weak limit is locally planar L², including on arbitrary
compact regions that meet limiting complementary components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem planarVolume_absolutelyContinuous_sphericalArea :
    (volume : Measure ℂ) ≪ planarSphericalArea :=
  withDensity_absolutelyContinuous'
    continuous_sphericalAreaDensity.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun z => (ENNReal.ofReal_pos.mpr (sphericalAreaDensity_pos z)).ne')

open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 theorem scalar_unit_spherical : ∀ᵐ z ∂planarSphericalArea, W.scalar z ∈ Icc 0 1 :=
  ae_mem_unitInterval_of_weak_limit
    (fun n => (W.fillings (W.subsequence n)).filled_measurable.aestronglyMeasurable)
    (fun n z => (W.fillings (W.subsequence n)).filled_mem z) W.scalar W.scalar_weak

 theorem scalar_unit : ∀ᵐ z ∂(volume : Measure ℂ), W.scalar z ∈ Icc 0 1 :=
  planarVolume_absolutelyContinuous_sphericalArea.ae_le W.scalar_unit_spherical

 theorem scalar_aestronglyMeasurable : AEStronglyMeasurable W.scalar (volume : Measure ℂ) :=
  (Lp.aestronglyMeasurable W.scalar).mono_ac planarVolume_absolutelyContinuous_sphericalArea

 theorem scalar_memLp_on {K : Set ℂ} (hK : volume K ≠ ∞) :
    MemLp W.scalar 2 (volume.restrict K) := by
  let : IsFiniteMeasure ((volume : Measure ℂ).restrict K) := isFiniteMeasure_restrict.mpr hK
  apply MemLp.of_bound W.scalar_aestronglyMeasurable.restrict 1
  filter_upwards [ae_restrict_of_ae W.scalar_unit] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
  exact hz.2

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Sobolev.SobolevGraphEnergy
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! The actual Sobolev graph energy is locally finite and outer regular.
A volume-null base set has zero graph energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma sobolevGraph_injective (u : EuclideanPlane → ℝ) : Injective (sobolevGraph u) := by
  intro x y h
  exact euclideanPlaneCoordinates.injective (congrArg Prod.fst h)

lemma sobolevGraphEnergy_finiteOnCompacts {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) :
    IsFiniteMeasureOnCompacts (sobolevGraphEnergy u W.weakGrad) := by
  constructor
  intro K hK
  have hS : IsCompact (euclideanPlaneCoordinates.symm '' (Prod.fst '' K)) :=
    (hK.image continuous_fst).image euclideanPlaneCoordinates.symm.continuous
  have hpre : IsCompact (sobolevGraph u ⁻¹' K) := by
    apply hS.of_isClosed_subset (hK.isClosed.preimage (sobolevGraph_continuous hu))
    intro x hx
    exact ⟨euclideanPlaneCoordinates x,⟨sobolevGraph u x,hx,rfl⟩,
      euclideanPlaneCoordinates.symm_apply_apply x⟩
  have hG : MemLp (fun x => |W.weakGrad x 0|+|W.weakGrad x 1|) 2 volume := by
    exact (show MemLp (fun x => W.weakGrad x 0) 2 volume by
      simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp 0).norm.add
      (show MemLp (fun x => W.weakGrad x 1) 2 volume by
        simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp 1).norm
  let : IsFiniteMeasure (volume.restrict (sobolevGraph u ⁻¹' K)) :=
    isFiniteMeasure_restrict.mpr hpre.measure_lt_top.ne
  have hi : IntegrableOn (fun x => 1+(|W.weakGrad x 0|+|W.weakGrad x 1|)^2)
      (sobolevGraph u ⁻¹' K) :=
    (integrable_const 1).add hG.integrable_sq.integrableOn
  rw [sobolevGraphEnergy,Measure.map_apply (sobolevGraph_continuous hu).measurable hK.measurableSet,
    withDensity_apply _ hpre.measurableSet,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
  exact ENNReal.ofReal_lt_top

lemma sobolevGraphEnergy_outerRegular {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) :
    (sobolevGraphEnergy u W.weakGrad).OuterRegular := by
  let : IsFiniteMeasureOnCompacts (sobolevGraphEnergy u W.weakGrad) :=
    sobolevGraphEnergy_finiteOnCompacts hu W
  infer_instance

lemma sobolevGraphEnergy_null {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (V : EuclideanPlane → EuclideanPlane) {E : Set EuclideanPlane}
    (hE : MeasurableSet E) (hnull : volume E = 0) :
    sobolevGraphEnergy u V (sobolevGraph u '' E) = 0 := by
  have hm := (sobolevGraph_continuous hu).measurableEmbedding (sobolevGraph_injective u)
  rw [sobolevGraphEnergy,Measure.map_apply hm.measurable (hm.measurableSet_image' hE),
    Set.preimage_image_eq _ (sobolevGraph_injective u)]
  exact withDensity_absolutelyContinuous volume _ hnull

end CircleDomainRigidity

end

end OAI

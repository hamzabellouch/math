import Mathlib
import OAI.Geometry.SmoothYau.Geometry.CoefficientGradientApply
import OAI.Geometry.SmoothYau.Geometry.CoordinateGradientPairScalarCorrection

namespace OAI

noncomputable section
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction CompactlySupported
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

def positiveIntegral : C_c(M,ℝ) →ₚ[ℝ] ℝ where
  toFun f := I.integral g f.toBoundedContinuousFunction
  map_add' f h := by
    change I.integral g (f.toBoundedContinuousFunction+h.toBoundedContinuousFunction) = _
    exact I.integral_add g _ _
  map_smul' c f := by
    change I.integral g (c • f.toBoundedContinuousFunction) = _
    exact I.integral_smul g c _
  monotone' f h hfh := I.integral_mono g hfh

def volumeMeasure : Measure M := RealRMK.rieszMeasure (I.positiveIntegral g)

instance volumeMeasure_finite : IsFiniteMeasure (I.volumeMeasure g) := by
  unfold volumeMeasure
  infer_instance

lemma mean_eq_volumeIntegral (f : M → ℝ) (hf : Continuous f) :
    I.mean g f = ∫ x, f x ∂I.volumeMeasure g := by
  let F : C_c(M,ℝ) := ⟨⟨f,hf⟩,HasCompactSupport.of_compactSpace f⟩
  exact (RealRMK.integral_rieszMeasure (I.positiveIntegral g) F).symm

instance volumeMeasure_openPos : Measure.IsOpenPosMeasure (I.volumeMeasure g) := by
  constructor
  intro O hO hne
  obtain ⟨x,hx⟩ := hne
  obtain ⟨V,hV,hxV,hVO⟩ := normal_exists_closure_subset isClosed_singleton hO
    (singleton_subset_iff.mpr hx)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ,E)) (n := ⊤) isClosed_singleton (t := V)
    (by simpa only [hV.interior_eq] using hxV)
  have hs : tsupport (fun y => χ y) ⊆ O := by
    apply (closure_mono (show support (fun y => χ y) ⊆ V from ?_)).trans hVO
    intro y hy
    by_contra hn
    exact hy (hχ0 y hn)
  have hx1 : χ x = 1 := hχ1.self_of_nhdsSet x (mem_singleton x)
  let f : C_c(M,ℝ) := ⟨⟨χ,χ.property.continuous⟩,HasCompactSupport.of_compactSpace _⟩
  have hp : 0 < I.positiveIntegral g f := I.integral_pos g
    (fun y => (hχb y).1) ⟨x,by change 0 < χ x; rw [hx1]; norm_num⟩
  exact ((ENNReal.ofReal_pos.mpr hp).trans_le
    (RealRMK.le_rieszMeasure_tsupport_subset (I.positiveIntegral g) (f := f) (fun y => hχb y) hs)).ne'

end MetricIntegralAtlas
end YauCounterexamples
end

end OAI

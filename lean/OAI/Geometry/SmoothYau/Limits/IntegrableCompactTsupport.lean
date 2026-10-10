import Mathlib
import OAI.Geometry.SmoothYau.Geometry.CoefficientGradientApply
import OAI.Geometry.SmoothYau.Geometry.RoundMetricExists

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma integrableOn_compact_tsupport {O : Set E} (hO : IsOpen O) {f : E → ℝ}
    (hf : ContinuousOn f O) (hc : HasCompactSupport f) (hs : tsupport f ⊆ O) :
    IntegrableOn f O := by
  apply IntegrableOn.of_inter_support hO.measurableSet
  exact ((hf.mono hs).integrableOn_compact hc).mono_set (fun _ hx => subset_tsupport f hx.2)

omit [T2Space M] in

theorem metricChartIntegral_green (g : SmoothMetric E M) (p : M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v)
    (huc : HasCompactSupport u) (hus : tsupport u ⊆ (chartAt E p).source) :
    metricChartIntegral g p (fun x => u x * laplaceBeltrami g v x) =
      -metricChartIntegral g p (coordinateGradientPair g u v) := by
  let f := realChartLocalize (E := E) p u
  let O := (chartAt E p).target
  let b := Module.finBasis ℝ E
  have hf : ContDiff ℝ ∞ f := contDiff_realChartLocalize p u huc hus hu
  have hfc : HasCompactSupport f := hasCompactSupport_realChartLocalize p u huc hus
  have hfs : tsupport f ⊆ O := tsupport_realChartLocalize_subset p u huc hus
  have hflux (i : CoordIndex E) : ContDiffOn ℝ ∞ (fun y => metricFlux g v p y i) O :=
    fun y hy => (contDiffAt_metricFlux hv g p hy i).contDiffWithinAt
  have hdf (i : CoordIndex E) : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (b i)) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hFi (i : CoordIndex E) : IntegrableOn (fun y => f y *
      fderiv ℝ (fun z => metricFlux g v p z i) y (b i)) O := by
    apply integrableOn_compact_tsupport (chartAt E p).open_target
    · apply hf.continuous.continuousOn.mul
      intro y hy
      exact (((contDiffAt_metricFlux hv g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiffAt_const).continuousAt.continuousWithinAt
    · exact hfc.mul_right
    · exact tsupport_mul_subset_left.trans hfs
  have hGi (i : CoordIndex E) : IntegrableOn (fun y => fderiv ℝ f y (b i) * metricFlux g v p y i) O := by
    apply integrableOn_compact_tsupport (chartAt E p).open_target
    · exact (hdf i).continuous.continuousOn.mul (hflux i).continuousOn
    · exact (hfc.fderiv_apply ℝ (b i)).mul_right
    · exact tsupport_mul_subset_left.trans ((tsupport_fderiv_apply_subset ℝ (b i)).trans hfs)
  have hleft : metricChartIntegral g p (fun x => u x * laplaceBeltrami g v x) =
      ∫ y in O, ∑ i, f y * fderiv ℝ (fun z => metricFlux g v p z i) y (b i) := by
    apply setIntegral_congr_fun (chartAt E p).open_target.measurableSet
    intro y hy
    dsimp only
    rw [laplaceBeltrami_inChart hv g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy]
    simp only [localLaplacian, ← Finset.mul_sum]
    rw [show f y = u ((chartAt E p).symm y) from realChartLocalize_eq p u hy]
    have hd : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
      (Real.sqrt_pos.2 (metricCoefficients_posDef g p hy).det_pos).ne'
    dsimp only [b]
    field_simp
  have hright : metricChartIntegral g p (coordinateGradientPair g u v) =
      ∫ y in O, ∑ i, fderiv ℝ f y (b i) * metricFlux g v p y i := by
    apply setIntegral_congr_fun (chartAt E p).open_target.measurableSet
    intro y hy
    dsimp only
    rw [coordinateGradientPair_inChart hu hv g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy]
    dsimp only [f]
    rw [realChartLocalize_fderiv p u hy]
    simp only [localGradientPair, metricFlux, Matrix.mulVec, dotProduct, Finset.mul_sum, b]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  rw [hleft, hright, integral_finsetSum _ (fun i _ => hFi i),
    integral_finsetSum _ (fun i _ => hGi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact local_integration_by_parts (chartAt E p).open_target hf hfc hfs (hflux i) (b i)
end YauCounterexamples

end

end OAI

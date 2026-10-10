import Mathlib
import OAI.Analysis.FourierExtension.RadialMeasure
import OAI.Analysis.FourierExtension.L2Fourier

namespace OAI

/-! Convex graph and affine Fourier bounds. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section
open Filter
open scoped Topology ContDiff
open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace ENNReal
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
open Set Filter
open scoped ENNReal InnerProductSpace
open scoped FourierTransform SchwartzMap ENNReal
open scoped ENNReal FourierTransform InnerProductSpace
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal

namespace DiagonalExtension.ConvexRadial
open MeasureTheory Set
open scoped ENNReal ContDiff

abbrev GraphSpace := WithLp 2 (E2 × ℝ)

def graphEmbedding (φ : E2 → ℝ) (ξ : E2) : GraphSpace :=
  WithLp.toLp 2 (ξ, φ ξ)

lemma graphEmbedding_continuous {φ : E2 → ℝ} (hφ : Continuous φ) :
    Continuous (graphEmbedding φ) :=
  (WithLp.prod_continuous_toLp 2 E2 ℝ).comp (continuous_id.prodMk hφ)

lemma graphEmbedding_pairMap (φ : E2 → ℝ) :
    GraphFourier.pairMap (graphEmbedding φ) = WithLp.toLp 2 ∘ pairGraph φ := by
  ext point
  rfl

lemma graphEmbedding_pairMap_le {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c) (hell : ∀ x v : E2,
      c * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v) :
    Measure.map (GraphFourier.pairMap (graphEmbedding φ)) (volume.prod volume) ≤
      ENNReal.ofReal (Real.pi / c) • (volume : Measure GraphSpace) := by
  rw [graphEmbedding_pairMap, ← Measure.map_map
    (WithLp.prod_continuous_toLp 2 E2 ℝ).measurable
    (pairGraph_continuous hφ.continuous).measurable]
  have H := Measure.map_mono (pairGraph_map_le hφ hc hell)
    (WithLp.prod_continuous_toLp 2 E2 ℝ).measurable
  simpa only [Measure.map_smul _ (WithLp.prod_continuous_toLp 2 E2 ℝ).measurable.aemeasurable,
    (WithLp.volume_preserving_toLp E2 ℝ).map_eq] using H

theorem convex_graph_L4 {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c) (hell : ∀ x v : E2,
      c * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v)
    {g : E2 → ℂ} (hg : MemLp g 2 volume) (hgc : HasCompactSupport g) :
    MemLp (GraphFourier.transform (graphEmbedding φ) g) 4 volume ∧
      eLpNorm (GraphFourier.transform (graphEmbedding φ) g) 4 volume ≤
        ENNReal.ofReal (Real.pi / c) ^ (1 / 4 : ℝ) * eLpNorm g 2 volume := by
  exact GraphFourier.memLp_four_and_bound (graphEmbedding_continuous hφ.continuous)
    ENNReal.ofReal_ne_top (graphEmbedding_pairMap_le hφ hc hell) hg hgc

end DiagonalExtension.ConvexRadial

namespace DiagonalExtension.AffineGraph
open MeasureTheory Set ConvexRadial
open scoped ENNReal NNReal
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]

def haarFactor (A : GraphSpace ≃L[ℝ] Y) : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.map A (volume : Measure GraphSpace)) (volume : Measure Y)

lemma map_affine (A : GraphSpace ≃L[ℝ] Y) (a : Y) :
    Measure.map (fun z => a + A z) (volume : Measure GraphSpace) =
      (haarFactor A : ℝ≥0∞) • (volume : Measure Y) := by
  have : Measure.IsAddHaarMeasure (Measure.map A (volume : Measure GraphSpace)) :=
    A.isAddHaarMeasure_map volume
  have hA := Measure.isAddLeftInvariant_eq_smul
    (Measure.map A (volume : Measure GraphSpace)) (volume : Measure Y)
  have he : (fun z => a + A z) = (fun y : Y => a + y) ∘ A := rfl
  have hm : Measurable (fun y : Y => a + y) := by fun_prop
  rw [he, ← Measure.map_map hm A.continuous.measurable,
    hA, Measure.map_smul _ hm.aemeasurable, Measure.IsAddLeftInvariant.map_add_left_eq_self]
  rfl

lemma pairMap_le (A : GraphSpace ≃L[ℝ] Y) (a : Y)
    {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hell : ∀ x v : E2, c * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v) :
    Measure.map (GraphFourier.pairMap (fun ξ => a + A (graphEmbedding φ ξ)))
        (volume.prod volume) ≤
      (ENNReal.ofReal (Real.pi / c) * (haarFactor A : ℝ≥0∞)) • volume := by
  have he : GraphFourier.pairMap (fun ξ => a + A (graphEmbedding φ ξ)) =
      (fun z => (a+a) + A z) ∘ GraphFourier.pairMap (graphEmbedding φ) := by
    ext z
    simp only [GraphFourier.pairMap, Function.comp_apply, map_add]
    abel
  have hm : Measurable (fun z : GraphSpace => (a+a) + A z) := by fun_prop
  rw [he, ← Measure.map_map hm
    (GraphFourier.pairMap_continuous (graphEmbedding_continuous hφ.continuous)).measurable]
  have H := Measure.map_mono (graphEmbedding_pairMap_le hφ hc hell)
    hm
  simpa only [Measure.map_smul _ hm.aemeasurable, map_affine, smul_smul] using H

theorem L4 (A : GraphSpace ≃L[ℝ] Y) (a : Y)
    {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hell : ∀ x v : E2, c * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v)
    {g : E2 → ℂ} (hg : MemLp g 2 volume) (hgc : HasCompactSupport g) :
    MemLp (GraphFourier.transform (fun ξ => a + A (graphEmbedding φ ξ)) g) 4 volume ∧
      eLpNorm (GraphFourier.transform (fun ξ => a + A (graphEmbedding φ ξ)) g) 4 volume ≤
        (ENNReal.ofReal (Real.pi / c) * (haarFactor A : ℝ≥0∞)) ^ (1/4 : ℝ) *
          eLpNorm g 2 volume := by
  apply GraphFourier.memLp_four_and_bound
    (continuous_const.add (A.continuous.comp (graphEmbedding_continuous hφ.continuous)))
    (by finiteness) (pairMap_le A a hφ hc hell) hg hgc

end DiagonalExtension.AffineGraph

end

end OAI

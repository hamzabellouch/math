import Mathlib
import OAI.Analysis.FourierExtension.GraphCharts
import OAI.Analysis.FourierExtension.AffineArea
import OAI.Analysis.FourierExtension.MeasureFourier

namespace OAI

/-! Global L4 extension bounds for compact curved surfaces. -/

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
open scoped ENNReal NNReal

namespace DiagonalExtension
open MeasureTheory Set
open scoped ENNReal NNReal

theorem IsSurface.exists_local_L4 {S : Set E3} (hS : IsSurface S) {a : E3} (ha : a ∈ S) :
    ∃ (V : Set E3) (C : ℝ≥0), IsOpen V ∧ a ∈ V ∧
      ∀ ν : Measure E3, ν ≤ (surfaceMeasure S).restrict V → ∀ f : E3 → ℂ,
        MemLp f 2 ν → MemLp (MeasureFourier.transform ν f) 4 volume ∧
          eLpNorm (MeasureFourier.transform ν f) 4 volume ≤ (C : ℝ≥0∞) * eLpNorm f 2 ν := by
  obtain ⟨A,φ,c,R,V,hc,hR,hφ,hess,hV,haV,hinc⟩ := LocalGraph.exists_local_graph hS ha
  let κ : ℝ≥0 := ⟨Real.pi/4, by positivity⟩
  obtain ⟨C,hC⟩ := AffineGraph.area_L4 A a hφ hc hess R κ
  refine ⟨V,C,hV,haV,?_⟩
  intro ν hν f hf
  apply hC ν _ f hf
  apply hν.trans
  have hnorm : (κ : ℝ≥0∞) = ENNReal.ofReal (Real.pi/4) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    rfl
  rw [hnorm,surfaceMeasure,Measure.restrict_restrict hV.measurableSet,inter_comm V S]
  exact Measure.restrict_mono_set _ hinc

theorem IsSurface.L4_negative {S : Set E3} (hS : IsSurface S) :
    ∃ C : ℝ≥0, ∀ f : E3 → ℂ, MemLp f 2 (surfaceMeasure S) →
      MemLp (MeasureFourier.transform (surfaceMeasure S) f) 4 volume ∧
      eLpNorm (MeasureFourier.transform (surfaceMeasure S) f) 4 volume ≤
        (C : ℝ≥0∞) * eLpNorm f 2 (surfaceMeasure S) := by
  classical
  have := hS.isFiniteMeasure
  choose V C hV haV hloc using (fun a : S => hS.exists_local_L4 a.property)
  have hcover : S ⊆ ⋃ a : S, V a := by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haV ⟨a,ha⟩⟩
  obtain ⟨t,ht⟩ := hS.1.elim_finite_subcover V hV hcover
  refine ⟨∑ a ∈ t, C a,?_⟩
  intro f hf
  have hcovered : ∀ᵐ y ∂surfaceMeasure S, ∃ i ∈ t, y ∈ V i := by
    filter_upwards [ae_restrict_mem hS.1.measurableSet] with y hy
    rcases mem_iUnion₂.mp (ht hy) with ⟨i,hi,hy⟩
    exact ⟨i,hi,hy⟩
  simpa only [ENNReal.ofNNReal_finsetSum] using MeasureFourier.finite_cover t V C
    (fun a => (hV a).measurableSet) (fun a _ => hloc a)
    (surfaceMeasure S) le_rfl hcovered f hf

lemma extension_eq_negative_transform (S : Set E3) (f : E3 → ℂ) :
    extension S f = MeasureFourier.transform (surfaceMeasure S) f ∘ Neg.neg := by
  ext x
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  simp only [inner_neg_right, neg_neg, Real.fourierChar_apply, fourierCharacter]
  rw [real_inner_comm]

theorem IsSurface.extension_L4 {S : Set E3} (hS : IsSurface S) :
    ∃ C : ℝ≥0, ∀ f : E3 → ℂ, MemLp f 2 (surfaceMeasure S) →
      MemLp (extension S f) 4 volume ∧
      eLpNorm (extension S f) 4 volume ≤ (C : ℝ≥0∞) * eLpNorm f 2 (surfaceMeasure S) := by
  obtain ⟨C,hC⟩ := hS.L4_negative
  refine ⟨C,?_⟩
  intro f hf
  obtain ⟨hm,hb⟩ := hC f hf
  rw [extension_eq_negative_transform]
  exact ⟨hm.comp_measurePreserving (Measure.measurePreserving_neg volume),
    (eLpNorm_comp_measurePreserving hm.aestronglyMeasurable
      (Measure.measurePreserving_neg volume)).le.trans hb⟩

end DiagonalExtension

end

end OAI

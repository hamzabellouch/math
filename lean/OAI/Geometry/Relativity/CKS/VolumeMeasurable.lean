import OAI.Geometry.Relativity.CKS.VolumeDefinitions

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
attribute [local instance] model_finiteDimensional model_borelSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

lemma chart_target_measurable [IsManifold I 1 M] (x : M) :
    MeasurableSet (extChartAt I x).target := by
  rw [extChartAt_target]
  exact ((chartAt H x).open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

variable [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]

def chartPreimage (x : M) (s : Set M) : Set E :=
  (extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target

lemma chartPreimage_measurable (x : M) {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet (chartPreimage x s) := by
  have h : Measurable ((extChartAt I x).target.domRestrict (extChartAt I x).symm) :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt_symm x)).measurable
  have hm := (chart_target_measurable x).subtype_image (hs.preimage h)
  convert hm using 1
  ext y
  simp [chartPreimage]

lemma localVolume_apply (g : Metric (M := M)) (x : M) {s : Set M} (hs : MeasurableSet s) :
    localVolume g x s = ∫⁻ y in chartPreimage x s, ENNReal.ofReal (chartDensity g x y) := by
  have hf := (continuousOn_extChartAt_symm x).aemeasurable
    (μ := (volume : Measure E)) (chart_target_measurable x)
  rw [localVolume, Measure.map_apply_of_aemeasurable
    (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hs, withDensity_apply']
  rw [← Measure.restrict_comm (chart_target_measurable x),
    Measure.restrict_restrict (chart_target_measurable x)]
  congr 1
  exact congrArg ((volume : Measure E).restrict) (inter_comm _ _)

end CKSIntrinsicVolume

end

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialVolumeWeak
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHilbertWeakSubsequence
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace OAI

/-! The radial H¹ volume observation is a compact operator. -/

open Set Filter Topology MeasureTheory
open scoped ENNReal
namespace DefocusingNLS

theorem spectralRadialValue_compact (R : ℝ) (hR : 0 < R) :
    IsCompactOperator (spectralRadialValue R) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : MeasureTheory.IsSeparable (radialPressureMeasure R) := inferInstance
  let : TopologicalSpace.SeparableSpace (SpectralRadialEnergy R) := inferInstance
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (spectralRadialValue R).toLinearMap zero_lt_one).mpr
  refine ⟨spectralRadialValue R '' Metric.closedBall 0 1,?_,subset_rfl⟩
  apply IsSeqCompact.isCompact
  intro f hf
  choose u hu hfu using hf
  have hub (n : ℕ) : ‖u n‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hu n
  obtain ⟨v,hv,φ,hφ,ht⟩ := spectralHilbert_weak_subsequence u 1 hub
  refine ⟨spectralRadialValue R v,⟨v,?_,rfl⟩,φ,hφ,?_⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  · have hdiff (n : ℕ) : ‖u (φ n)-v‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hub (φ n)])
    have hweak (L : SpectralRadialEnergy R →L[ℂ] ℂ) :
        Tendsto (fun n => L (u (φ n)-v)) atTop (𝓝 0) := by
      simpa only [map_sub,sub_self] using (ht L).sub_const (L v)
    have hz := spectralRadialVolume_weakNull R hR (fun n => u (φ n)-v) 2 hdiff hweak
    have h := hz.add_const (spectralRadialValue R v)
    simpa only [map_sub,sub_add_cancel,zero_add,hfu,Function.comp_def] using h

end DefocusingNLS

end OAI

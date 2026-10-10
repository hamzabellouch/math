import OAI.Analysis.LipschitzHilbert.Estimates.ReferenceChart
import OAI.Analysis.LipschitzHilbert.Fourier.LineCountSlab

namespace OAI

/-! The measurable planar exceptional set attached to one reference top. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

def referenceException (T : SlopeBox) (N : ℝ × ℝ → ℝ≥0∞) (K lambda : ℝ) : Set (ℝ × ℝ) :=
  T.referenceChart '' LipschitzHilbert.lineCountSlab N (T.witnessInterval K)
    (Icc (-K * T.width) (K * T.width)) lambda

theorem measurableSet_referenceException (T : SlopeBox) (N : ℝ × ℝ → ℝ≥0∞)
    (hN : Measurable N) (K lambda : ℝ) : MeasurableSet (T.referenceException N K lambda) := by
  apply T.referenceChart.measurableSet_image.mpr
  exact LipschitzHilbert.measurableSet_lineCountSlab N hN _ _ measurableSet_Icc measurableSet_Icc lambda

theorem referenceException_measure_bound (T : SlopeBox) (N : ℝ × ℝ → ℝ≥0∞)
    (hN : Measurable N) {K lambda M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (htail : ∀ v ∈ Icc (-K * T.width) (K * T.width),
      volume.real ({x | ENNReal.ofReal lambda < N (v, x)} ∩ T.witnessInterval K) ≤ M) :
    (volume.prod volume).real (T.referenceException N K lambda) ≤ M * (2 * K * T.width) := by
  have harea : (volume.prod volume).real (T.referenceException N K lambda) =
      (volume.prod volume).real (LipschitzHilbert.lineCountSlab N (T.witnessInterval K)
        (Icc (-K * T.width) (K * T.width)) lambda) :=
    congrArg ENNReal.toReal (T.referenceChart_image_measure _)
  rw [harea]
  have h := LipschitzHilbert.lineCountSlab_measure_bound N hN _ _ measurableSet_Icc measurableSet_Icc
    measure_Icc_lt_top.ne measure_Icc_lt_top.ne hM htail
  have hlen : volume.real (Icc (-K * T.width) (K * T.width)) = 2 * K * T.width := by
    rw [Real.volume_real_Icc_of_le (by nlinarith [T.width_pos])]
    ring
  simpa only [hlen, witnessInterval] using h

/-- At every significant point outside this fixed exceptional set, the
reference-line count is below the chosen threshold. -/
theorem count_le_outside_referenceException (T : SlopeBox) (N : ℝ × ℝ → ℝ≥0∞)
    {K lambda : ℝ} {z : ℝ × ℝ} (hz : T.radius z ≤ K)
    (hout : z ∉ T.referenceException N K lambda) :
    N ((T.referenceChart.symm z).2, z.1) ≤ ENNReal.ofReal lambda := by
  apply le_of_not_gt
  intro hlt
  apply hout
  refine ⟨T.referenceChart.symm z, ?_, T.referenceChart.apply_symm_apply z⟩
  refine ⟨T.significant_mem_referenceRectangle hz, ?_⟩
  exact hlt

end LipschitzHilbert.SlopeBox

end

end OAI

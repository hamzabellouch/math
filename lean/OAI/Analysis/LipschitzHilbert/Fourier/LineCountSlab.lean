import OAI.Analysis.LipschitzHilbert.Fourier.LineCounting
import OAI.Analysis.LipschitzHilbert.Estimates.SectionMeasure

namespace OAI

/-! Integrating the line-counting tail across a finite transverse interval. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

def lineCountSlab (N : ℝ × ℝ → ℝ≥0∞) (U V : Set ℝ) (lambda : ℝ) : Set (ℝ × ℝ) :=
  (U ×ˢ V) ∩ {z | ENNReal.ofReal lambda < N (z.2, z.1)}

theorem measurableSet_lineCountSlab (N : ℝ × ℝ → ℝ≥0∞) (hN : Measurable N)
    (U V : Set ℝ) (hU : MeasurableSet U) (hV : MeasurableSet V) (lambda : ℝ) :
    MeasurableSet (lineCountSlab N U V lambda) :=
  (hU.prod hV).inter (measurableSet_lt measurable_const (hN.comp measurable_swap))

theorem lineCountSlab_measure_bound (N : ℝ × ℝ → ℝ≥0∞) (hN : Measurable N)
    (U V : Set ℝ) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUf : volume U ≠ ∞) (hVf : volume V ≠ ∞) {lambda M : ℝ} (hM : 0 ≤ M)
    (htail : ∀ y ∈ V, volume.real ({x | ENNReal.ofReal lambda < N (y, x)} ∩ U) ≤ M) :
    (volume.prod volume).real (lineCountSlab N U V lambda) ≤ M * volume.real V := by
  apply section_measure_bound _ (measurableSet_lineCountSlab N hN U V hU hV lambda)
    U V hV hUf hVf inter_subset_left hM
  intro y hy
  have heq : (fun x => (x, y)) ⁻¹' lineCountSlab N U V lambda =
      {x | ENNReal.ofReal lambda < N (y, x)} ∩ U := by
    ext x
    simp only [lineCountSlab, mem_preimage, mem_inter_iff, mem_prod, hy, and_true, mem_ofPred_eq]
    exact and_comm
  rw [heq]
  exact htail y hy

end LipschitzHilbert

end

end OAI

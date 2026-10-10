import OAI.Analysis.CircleDomains.Rigidity.EnclosedCircleChords
import OAI.Analysis.CircleDomains.Rigidity.AxialLineDifferentiation
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! The integral on an actual outer chord is the corresponding slice
of the globally zero-extended source density. -/
open Set Function Filter MeasureTheory Metric
noncomputable section
namespace CircleDomainRigidity

 theorem axial_closed_disk_integral (i : Fin 2) (y : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hy : y ∈ Icc (-R) R) {U : Set ℂ} (hU : MeasurableSet U) (q : ℂ → ℝ) :
    (∫ x in Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2 ∩
        {x | complexCoordinateLine i y x ∈ U}, q (complexCoordinateLine i y x)) =
      ∫ x, (U ∩ closedBall 0 R).indicator q (complexCoordinateLine i y x) := by
  classical
  have hmem (x : ℝ) : complexCoordinateLine i y x ∈ closedBall 0 R ↔
      x ∈ Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2 :=
    mem_closedBall_iff_mem_axialChord i 0 hR (by simpa [transverseCoordinate] using hy)
  have hset : MeasurableSet (Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2 ∩
      {x | complexCoordinateLine i y x ∈ U}) :=
    measurableSet_Icc.inter (hU.preimage (complexCoordinateLine_contDiff i y).continuous.measurable)
  rw [← integral_indicator hset]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hu : complexCoordinateLine i y x ∈ U <;>
    by_cases hx : x ∈ Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2 <;>
    simp [hu,hx,hmem]

end CircleDomainRigidity

end

end OAI

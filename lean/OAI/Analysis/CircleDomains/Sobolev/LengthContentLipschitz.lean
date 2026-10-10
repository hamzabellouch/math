import OAI.Analysis.CircleDomains.Probability.LengthContentNull
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! Lipschitz transport of the one-dimensional content used by coordinate
rescalings in the local Sobolev graph estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma lengthContent_image_le {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    {f : X → Y} {L : ℝ≥0} (hf : LipschitzWith L f) (A : Set X) :
    lengthContent (f '' A) ≤ (L : ℝ≥0∞)*lengthContent A := by
  have hh : OuterMeasure.comap f (lengthContent : OuterMeasure Y) ≤
      (L : ℝ≥0∞) • (lengthContent : OuterMeasure X) := by
    simp only [lengthContent]
    rw [OuterMeasure.smul_ofFunction ENNReal.coe_ne_top]
    apply OuterMeasure.le_ofFunction.mpr
    intro S
    change lengthContent (f '' S) ≤ (L : ℝ≥0∞)*ediam S
    exact (lengthContent_le_ediam _).trans (hf.ediam_image_le S)
  simpa only [OuterMeasure.comap_apply, smul_apply, smul_eq_mul] using hh A

end CircleDomainRigidity

end

end OAI

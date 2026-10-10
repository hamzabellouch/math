import OAI.Analysis.CircleDomains.Sobolev.LocalGradientIntegrability

namespace OAI

/-! Local L2 hypotheses supply global completed measurability of each weak partial. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma local_partial_aestronglyMeasurable {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (i : Fin 2) :
    AEStronglyMeasurable (fun p => V p i) volume := by
  have h : AEStronglyMeasurable (fun p => V p i)
      (volume.restrict (⋃ n : ℕ, ball (0 : EuclideanPlane) n)) :=
    AEStronglyMeasurable.iUnion (fun n : ℕ => (hLp n i).aestronglyMeasurable)
  simpa only [Metric.iUnion_ball_nat, Measure.restrict_univ] using h

end CircleDomainRigidity

end

end OAI

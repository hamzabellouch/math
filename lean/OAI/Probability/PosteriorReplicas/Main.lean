import OAI.Probability.PosteriorReplicas.Information.HaarStateBound
import OAI.Probability.PosteriorReplicas.Information.HeadlineInformation
import OAI.Probability.PosteriorReplicas.Learners.HaarLawIdentification
import OAI.Probability.PosteriorReplicas.Learners.JointLawBridge

namespace OAI

namespace PosteriorReplicas
universe u

theorem main : EqualLabelMeasureIdentity ∧ EqualLabelVersions ∧
    GaussianReplicaBlock ∧ DistanceReplicaBlock ∧ HaarReplicaBlock ∧
    SyntheticReplicaBlock ∧ IncidenceReplicaBlock ∧
    PosteriorRegression.SubquadraticMemory.{u} :=
  ⟨equalLabelMeasureIdentity, equalLabelVersions, gaussianReplicaBlock,
    distanceReplicaBlock, haarReplicaBlock, syntheticReplicaBlock,
    incidenceReplicaBlock, PosteriorRegression.subquadratic_memory⟩

theorem source_main : EqualLabelMeasureIdentity ∧ EqualLabelVersions ∧
    GaussianReplicaBlock ∧ DistanceReplicaBlock ∧ HaarReplicaBlock ∧
    SyntheticReplicaBlock ∧ IncidenceReplicaBlock ∧
    PosteriorRegression.KernelSubquadraticMemory.{u} :=
  ⟨equalLabelMeasureIdentity, equalLabelVersions, gaussianReplicaBlock,
    distanceReplicaBlock, haarReplicaBlock, syntheticReplicaBlock,
    incidenceReplicaBlock, PosteriorRegression.kernel_subquadratic_memory⟩
end PosteriorReplicas

end OAI

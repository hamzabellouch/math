import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientManifold
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientCore
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! Smooth localization of the actual compact quotient core into the
constructed arithmetic coordinate charts. -/
noncomputable section
open scoped MatrixGroups Manifold ContDiff
namespace CubicFirstMoment

lemma cubicThetaCore_smooth_partition (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    ∃ f : SmoothPartitionOfUnity CubicThetaQuotient (𝓘(ℝ,ℂ × ℝ)) CubicThetaQuotient
        (cubicThetaQuotientCore S V),
      f.IsSubordinate (fun q => (cubicThetaQuotientChart q).source) := by
  apply SmoothPartitionOfUnity.exists_isSubordinate _
    (cubicThetaQuotientCore_compact S V).isClosed
  · intro q
    exact (cubicThetaQuotientChart q).open_source
  · intro q _
    exact Set.mem_iUnion.mpr ⟨q,cubicThetaQuotientChart_source q⟩

end CubicFirstMoment

end

end OAI

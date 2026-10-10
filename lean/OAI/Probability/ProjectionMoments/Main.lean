import OAI.Probability.ProjectionMoments.SphereWeights

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open NoiselessRegression NoiselessRegression.FiniteKernelLearner
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace ProjectionMoments

theorem main : MainStatement.{u} := by
  refine ⟨integrated_frame_moment, normalized_unitBall_moment, all_radii_sphere_moment,
    positive_family_cap_domination, riesz_deterministic_offsets, one_block_all_radii,
    NoiselessRegression.FiniteKernelLearner.haar_success,
    NoiselessRegression.FiniteKernelLearner.riesz_success,
    NoiselessRegression.FiniteKernelLearner.cap_fixed_stop,
    NoiselessRegression.FiniteKernelLearner.cap_total_success,
    NoiselessRegression.FiniteKernelLearner.cap_fixed_stop_asymptotic,
    NoiselessRegression.FiniteKernelLearner.cap_total_success_asymptotic, ?_,
    NoiselessRegression.FiniteKernelLearner.subquadratic_memory_with_pointwise,
    NoiselessRegression.FiniteKernelLearner.fixed_quadratic_memory⟩
  intro d M T hd K hK
  exact K.exists_equivalent_tape hK hd

end ProjectionMoments

end

end

end OAI

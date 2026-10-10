import OAI.Analysis.PureInfiniteness.RelativeOneStep

namespace OAI

/-! The actual point-norm topology on maps, and the closure step in KR02 7.20. -/

noncomputable section
open Set Filter Topology

namespace WeakPureInfiniteness

variable {B D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]

omit [NonUnitalCStarAlgebra B] in
lemma finite_approximation_of_mem_closure {S : Set (B → D)} {T : B → D}
    (hT : T ∈ closure S) (F : Finset B) (ε : ℝ) (hε : 0 < ε) :
    ∃ R ∈ S, ∀ b ∈ F, ‖T b - R b‖ < ε := by
  let V : Set (B → D) := (F : Set B).pi (fun b => Metric.ball (T b) ε)
  have hV : V ∈ 𝓝 T := set_pi_mem_nhds F.finite_toSet
    (fun _ _ => Metric.ball_mem_nhds _ hε)
  obtain ⟨R, hRV, hRS⟩ := mem_closure_iff_nhds.mp hT V hV
  refine ⟨R, hRS, fun b hb => ?_⟩
  have hr := hRV b hb
  simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hr

lemma approximatelyOneStepAlong_of_mem_closure (β : B →⋆ₙₐ[ℂ] D)
    {S : Set (B → D)} (hS : ∀ R ∈ S, ApproximatelyOneStepAlong β R)
    {T : B → D} (hT : T ∈ closure S) : ApproximatelyOneStepAlong β T := by
  apply ApproximatelyOneStepAlong.of_pointNorm_approximation β T
  intro F ε hε
  obtain ⟨R, hRS, hRT⟩ := finite_approximation_of_mem_closure hT F ε hε
  exact ⟨R, hS R hRS, hRT⟩

end WeakPureInfiniteness

end

end OAI

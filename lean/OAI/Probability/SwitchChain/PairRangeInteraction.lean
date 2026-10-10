import OAI.Probability.SwitchChain.OrthogonalPairResampling
import OAI.Probability.SwitchChain.ProjectionRangeInteraction

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem pair_interaction_of_correlated_ranges
    {n : ℕ} {d : Fin n → ℕ} (a b : Finset (Fin n))
    (G R S : StateSpace n d →L[ℝ] StateSpace n d)
    (hGs : G.toLinearMap.IsSymmetric)
    (hRs : R.toLinearMap.IsSymmetric) (hSs : S.toLinearMap.IsSymmetric)
    (hGi : ∀ f, G (G f) = G f)
    (hGa : ∀ f, G (expectation n d a f) = 0)
    (hGb : ∀ f, G (expectation n d b f) = 0)
    (hR : ∀ f, R (fluctuation n d a (expectation n d b (expectation n d a f))) =
      fluctuation n d a (expectation n d b (expectation n d a f)))
    (hS : ∀ f, S (fluctuation n d b (expectation n d a (expectation n d b f))) =
      fluctuation n d b (expectation n d a (expectation n d b f)))
    (f : StateSpace n d) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪fluctuation n d a f, fluctuation n d b f⟫ := by
  apply ProjectionRangeInteraction.interaction_of_correlated_error_ranges
    (expectation n d a).toLinearMap (expectation n d b).toLinearMap
    G.toLinearMap R.toLinearMap S.toLinearMap
    (expectation_isSymmetric a) (expectation_isSymmetric b) hGs hRs hSs
    (expectation_idempotent a) (expectation_idempotent b) hGi hGa hGb
    (fun z => ?_) (fun z => ?_) f |>.trans_eq
      (by simp only [ContinuousLinearMap.coe_coe, fluctuation_eq_sub])
  · simpa only [fluctuation_eq_sub, ContinuousLinearMap.coe_coe] using hR z
  · simpa only [fluctuation_eq_sub, ContinuousLinearMap.coe_coe] using hS z

end Problem315.PairResampling

end

end OAI

import OAI.Probability.FreeIsing.Energy.ResponseSourceInvariance
import OAI.Probability.FreeIsing.Trees.CoordinateResponse

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367

namespace TreePathResponse

theorem response_update_eq_sourceResponse {d : ℕ} (beta : ℝ)
    (h : TreeVertex d → ℝ) {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hr : r ∈ E) (v : TreeVertex d) (t : ℝ) :
    response beta (Function.update h r t) E r v =
      FinitePosterior.sourceResponse
        (fun eta => GibbsLeaf.energy beta (Function.update h r 0) E (extendFiniteSpin E eta))
        (fun eta => spinSign (extendFiniteSpin E eta r))
        (fun eta => spinSign (extendFiniteSpin E eta v)) t := by
  classical
  have he (f : (E → IsingSpin) → ℝ) :
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta (Function.update h r t) E (extendFiniteSpin E eta)) f =
      FinitePosterior.mean
        (fun eta => GibbsLeaf.energy beta (Function.update h r 0) E (extendFiniteSpin E eta))
        (fun eta => spinSign (extendFiniteSpin E eta r)) f t := by
    simpa only [Function.update_self, zero_add, Function.update_idem] using
      expectation_update_field beta (Function.update h r 0) hr f t
  unfold response covariance mean LeafGibbs.covariance
  simp only [he, FinitePosterior.sourceResponse, FinitePosterior.tiltCovariance, mul_comm]

theorem response_update_source {d : ℕ} (beta : ℝ)
    (h : TreeVertex d → ℝ) {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hr : r ∈ E) (v : TreeVertex d) (t u : ℝ) :
    response beta (Function.update h r t) E r v =
      response beta (Function.update h r u) E r v := by
  classical
  let : Nonempty (E → IsingSpin) := ⟨fun _ => .pos⟩
  rw [response_update_eq_sourceResponse beta h hr v t,
    response_update_eq_sourceResponse beta h hr v u]
  apply FinitePosterior.sourceResponse_eq
  · intro eta
    cases extendFiniteSpin E eta r <;> simp [spinSign]
  · refine ⟨fun _ => .neg, ?_⟩
    rw [extendFiniteSpin_apply E (fun _ => .neg) ⟨r, hr⟩]
    rfl
  · refine ⟨fun _ => .pos, ?_⟩
    rw [extendFiniteSpin_apply E (fun _ => .pos) ⟨r, hr⟩]
    rfl

theorem response_eq_update_source_zero {d : ℕ} (beta : ℝ)
    (h : TreeVertex d → ℝ) {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hr : r ∈ E) (v : TreeVertex d) :
    response beta h E r v = response beta (Function.update h r 0) E r v := by
  simpa only [Function.update_eq_self] using response_update_source beta h hr v (h r) 0

theorem response_eq_of_eq_off_source {d : ℕ} (beta : ℝ)
    {h k : TreeVertex d → ℝ} {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hr : r ∈ E) (heq : ∀ w, w ≠ r → h w = k w) (v : TreeVertex d) :
    response beta h E r v = response beta k E r v := by
  classical
  rw [response_eq_update_source_zero beta h hr v,
    response_eq_update_source_zero beta k hr v]
  have hupdate : Function.update h r 0 = Function.update k r 0 := by
    funext w
    by_cases hw : w = r
    · simp [hw]
    · simp only [Function.update_of_ne hw, heq w hw]
  rw [hupdate]

end TreePathResponse
end Problem367

end

end OAI

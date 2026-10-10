import OAI.Probability.FreeIsing.Trees.CoordinateResponse
import OAI.Probability.FreeIsing.Trees.LeafCovariance

namespace OAI

noncomputable section

namespace Problem367.TreePathResponse

theorem mean_erase {d : ℕ} {D : Finset (TreeVertex d)} {v p u : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (hu : u ∈ D.erase v) :
    mean beta h D u = mean beta
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v))) (D.erase v) u := by
  have hm := tree_gibbs_expectation_erase beta h hv hp hedges
    (fun eta => spinSign (eta ⟨u, hu⟩))
  change LeafGibbs.expectation _ (fun eta : D → IsingSpin =>
    spinSign (eta ⟨u, (Finset.mem_erase.mp hu).2⟩)) = _ at hm
  simpa only [mean, extendFiniteSpin, dite_eq_left hu,
    dite_eq_left (Finset.mem_erase.mp hu).2] using hm

theorem covariance_erase {d : ℕ} {D : Finset (TreeVertex d)} {v p u w : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (hu : u ∈ D.erase v) (hw : w ∈ D.erase v) :
    covariance beta h D u w = covariance beta
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v))) (D.erase v) u w := by
  have hm := tree_gibbs_covariance_erase beta h hv hp hedges
    (fun eta => spinSign (eta ⟨u, hu⟩)) (fun eta => spinSign (eta ⟨w, hw⟩))
  change LeafGibbs.covariance _ (fun eta : D → IsingSpin =>
    spinSign (eta ⟨u, (Finset.mem_erase.mp hu).2⟩))
    (fun eta => spinSign (eta ⟨w, (Finset.mem_erase.mp hw).2⟩)) = _ at hm
  simpa only [covariance, extendFiniteSpin, dite_eq_left hu,
    dite_eq_left (Finset.mem_erase.mp hu).2, dite_eq_left hw,
    dite_eq_left (Finset.mem_erase.mp hw).2] using hm

theorem response_erase {d : ℕ} {D : Finset (TreeVertex d)} {v p u w : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (hu : u ∈ D.erase v) (hw : w ∈ D.erase v) :
    response beta h D u w = response beta
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v))) (D.erase v) u w := by
  rw [response, response, covariance_erase beta h hv hp hedges hu hw,
    mean_erase beta h hv hp hedges hu]

theorem response_leaf {d : ℕ} {D : Finset (TreeVertex d)} {v p u : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (hu : u ∈ D.erase v) :
    response beta h D u v =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) (h v)) *
        response beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
          (D.erase v) u p := by
  have hc := tree_gibbs_covariance_leaf beta h hv hp hedges
    (fun eta => spinSign (eta ⟨u, hu⟩))
  change LeafGibbs.covariance _ (fun eta : D → IsingSpin =>
    spinSign (eta ⟨u, (Finset.mem_erase.mp hu).2⟩))
    (fun eta => spinSign (eta ⟨v, hv⟩)) = _ *
    LeafGibbs.covariance _ (fun eta : D → IsingSpin =>
      spinSign (eta ⟨u, (Finset.mem_erase.mp hu).2⟩))
      (fun eta => spinSign (eta ⟨p, (Finset.mem_erase.mp hp).2⟩)) at hc
  have hc' : covariance beta h D u v =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) (h v)) *
        covariance beta h D u p := by
    simpa only [covariance, extendFiniteSpin, dite_eq_left hv,
      dite_eq_left (Finset.mem_erase.mp hu).2,
      dite_eq_left (Finset.mem_erase.mp hp).2] using hc
  rw [response, hc', covariance_erase beta h hv hp hedges hu hp,
    mean_erase beta h hv hp hedges hu, response, mul_div_assoc]

theorem response_self {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {u : TreeVertex d} (hu : u ∈ D) :
    response beta h D u u = 1 := by
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .pos⟩
  have hc : covariance beta h D u u = 1 - mean beta h D u ^ 2 := by
    simp only [covariance, LeafGibbs.covariance, spinSign_mul_self,
      LeafGibbs.expectation_const, mean, pow_two]
  rw [response, hc, div_self (variance_pos beta h hu).ne']

end Problem367.TreePathResponse

end

end OAI

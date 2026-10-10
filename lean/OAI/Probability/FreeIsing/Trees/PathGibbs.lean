import OAI.Probability.FreeIsing.Energy.FiniteLeafCovariance
import OAI.Probability.FreeIsing.Gibbs.Leaf
import OAI.Probability.FreeIsing.Posterior.PathPosteriorResponse
import OAI.Probability.FreeIsing.Trees.PathCylinders

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.TreePathGibbs

def vertexEquiv {d : ℕ} (v : TreeVertex d) :
    Fin (v.1.length + 1) ≃ ConnectedHull.vertices v :=
  Equiv.ofBijective
    (fun i => ⟨ConnectedHull.path v i,
      ConnectedHull.prefix_mem_vertices v (Nat.le_of_lt_succ i.isLt)⟩)
    ⟨fun i j hij => ConnectedHull.path_injective v (congrArg Subtype.val hij), by
      intro u
      obtain ⟨i, hi, he⟩ := ConnectedHull.mem_vertices.mp u.property
      exact ⟨⟨i, by omega⟩, Subtype.ext he⟩⟩

@[simp] theorem vertexEquiv_val {d : ℕ} (v : TreeVertex d)
    (i : Fin (v.1.length + 1)) :
    (vertexEquiv v i).val = ConnectedHull.path v i := rfl

def assignmentEquiv {d : ℕ} (v : TreeVertex d) :
    (ConnectedHull.vertices v → IsingSpin) ≃ (Fin (v.1.length + 1) → IsingSpin) where
  toFun eta i := eta (vertexEquiv v i)
  invFun s u := s ((vertexEquiv v).symm u)
  left_inv eta := by
    funext u
    simp
  right_inv s := by
    funext i
    simp

theorem extend_assignment_path {d : ℕ} (v : TreeVertex d)
    (eta : ConnectedHull.vertices v → IsingSpin) (i : Fin (v.1.length + 1)) :
    extendFiniteSpin (ConnectedHull.vertices v) eta (ConnectedHull.path v i) =
      assignmentEquiv v eta i := by
  exact extendFiniteSpin_apply (ConnectedHull.vertices v) eta (vertexEquiv v i)

theorem extend_assignment_symm_path {d : ℕ} (v : TreeVertex d)
    (s : Fin (v.1.length + 1) → IsingSpin) (i : Fin (v.1.length + 1)) :
    extendFiniteSpin (ConnectedHull.vertices v) ((assignmentEquiv v).symm s)
      (ConnectedHull.path v i) = s i := by
  rw [extend_assignment_path, Equiv.apply_symm_apply]

theorem energy_eq_path {d : ℕ} (v : TreeVertex d) (beta : ℝ)
    (h : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    GibbsLeaf.energy beta h (ConnectedHull.vertices v) eta =
      FinitePosterior.fieldEnergy (PathPosterior.interaction beta v.1.length)
        (PathPosterior.spin v.1.length) (fun i => h (ConnectedHull.path v i))
        (fun i => eta (ConnectedHull.path v i)) := by
  classical
  unfold GibbsLeaf.energy
  rw [ConnectedHull.inducedEdges_vertices, ConnectedHull.vertices_eq_image_path]
  rw [Finset.sum_image]
  · rw [Finset.sum_image]
    · unfold FinitePosterior.fieldEnergy PathPosterior.interaction PathPosterior.spin
      simp only [ConnectedHull.pathEdge]
      ring
    · exact fun _ _ _ _ he => ConnectedHull.pathEdge_injective v he
  · exact fun _ _ _ _ he => ConnectedHull.path_injective v he

theorem expectation_eq_path {d : ℕ} (v : TreeVertex d) (beta : ℝ)
    (h : TreeVertex d → ℝ) (f : (Fin (v.1.length + 1) → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h (ConnectedHull.vertices v)
        (extendFiniteSpin (ConnectedHull.vertices v) eta))
      (fun eta => f (assignmentEquiv v eta)) =
    FinitePathGibbs.mean beta (h (ConnectedHull.path v 0))
      (PathPosterior.childFields (fun i => h (ConnectedHull.path v i))) v.1.length f := by
  rw [PathPosterior.mean_eq_fieldMean beta v.1.length
    (fun i => h (ConnectedHull.path v i)) f]
  unfold LeafGibbs.expectation FinitePosterior.fieldMean
  rw [← (assignmentEquiv v).symm.sum_comp
    (fun eta => f (assignmentEquiv v eta) *
      Real.exp (GibbsLeaf.energy beta h (ConnectedHull.vertices v)
        (extendFiniteSpin (ConnectedHull.vertices v) eta)))]
  rw [← (assignmentEquiv v).symm.sum_comp
    (fun eta => Real.exp (GibbsLeaf.energy beta h (ConnectedHull.vertices v)
      (extendFiniteSpin (ConnectedHull.vertices v) eta)))]
  simp only [Equiv.apply_symm_apply, energy_eq_path, extend_assignment_symm_path]

theorem covariance_eq_path {d : ℕ} (v : TreeVertex d) (beta : ℝ)
    (h : TreeVertex d → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h (ConnectedHull.vertices v)
        (extendFiniteSpin (ConnectedHull.vertices v) eta))
      (fun eta => spinSign (extendFiniteSpin (ConnectedHull.vertices v) eta (ConnectedHull.root d)))
      (fun eta => spinSign (extendFiniteSpin (ConnectedHull.vertices v) eta v)) =
    FinitePathGibbs.endpointCovariance beta (h (ConnectedHull.path v 0))
      (PathPosterior.childFields (fun i => h (ConnectedHull.path v i))) v.1.length := by
  have hfirst (eta : ConnectedHull.vertices v → IsingSpin) :
      extendFiniteSpin (ConnectedHull.vertices v) eta (ConnectedHull.root d) =
        assignmentEquiv v eta 0 := by
    simpa only [ConnectedHull.path_zero] using extend_assignment_path v eta 0
  have hlast (eta : ConnectedHull.vertices v → IsingSpin) :
      extendFiniteSpin (ConnectedHull.vertices v) eta v =
        assignmentEquiv v eta (Fin.last v.1.length) := by
    simpa only [ConnectedHull.path_last] using
      extend_assignment_path v eta (Fin.last v.1.length)
  simp only [hfirst, hlast]
  unfold LeafGibbs.covariance FinitePathGibbs.endpointCovariance
  rw [expectation_eq_path v beta h (fun s => spinSign (s 0) * spinSign (s (Fin.last v.1.length))),
    expectation_eq_path v beta h (fun s => spinSign (s 0)),
    expectation_eq_path v beta h (fun s => spinSign (s (Fin.last v.1.length)))]

theorem covariance_mem_Icc {d : ℕ} (v : TreeVertex d) {beta : ℝ}
    (hbeta : 0 ≤ beta) (h : TreeVertex d → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h (ConnectedHull.vertices v)
        (extendFiniteSpin (ConnectedHull.vertices v) eta))
      (fun eta => spinSign (extendFiniteSpin (ConnectedHull.vertices v) eta (ConnectedHull.root d)))
      (fun eta => spinSign (extendFiniteSpin (ConnectedHull.vertices v) eta v)) ∈
      Set.Icc 0 (Real.tanh beta ^ v.1.length) := by
  rw [covariance_eq_path]
  exact FinitePathGibbs.endpointCovariance_mem_Icc hbeta _ _ _

end Problem367.TreePathGibbs

end

end OAI

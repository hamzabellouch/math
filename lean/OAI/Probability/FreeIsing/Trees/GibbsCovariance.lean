import OAI.Probability.FreeIsing.Trees.AutDistance
import OAI.Probability.FreeIsing.Trees.GibbsAutomorphism

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_covariance_bounds {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) (h : TreeVertex d → ℝ)
    {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D) :
    0 ≤ LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta ⟨u, hu⟩)) (fun eta => spinSign (eta ⟨v, hv⟩)) ∧
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta ⟨u, hu⟩)) (fun eta => spinSign (eta ⟨v, hv⟩)) ≤
        Real.tanh beta ^ reducedWordDistance u.1 v.1 := by
  obtain ⟨g, hg, hdist⟩ := exists_treeAut_to_root_distance u
  simpa only [hdist] using
    TreeGibbsAut.covariance_bounds_of_reroot hbeta D hD h ⟨u, hu⟩ ⟨v, hv⟩ g hg

theorem abs_tree_gibbs_covariance_le {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) (h : TreeVertex d → ℝ)
    {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D) :
    |LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta ⟨u, hu⟩)) (fun eta => spinSign (eta ⟨v, hv⟩))| ≤
        Real.tanh beta ^ reducedWordDistance u.1 v.1 := by
  have hb := tree_gibbs_covariance_bounds hbeta hD h hu hv
  rw [abs_of_nonneg hb.1]
  exact hb.2

end Problem367

end

end OAI

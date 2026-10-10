import OAI.Probability.FreeIsing.Trees.AutDistance
import OAI.Probability.FreeIsing.Trees.CoordinateResponse
import OAI.Probability.FreeIsing.Trees.GibbsAutomorphism

namespace OAI

noncomputable section

namespace Problem367.TreePathResponse

theorem mean_relabel {d : ℕ} (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u : D) :
    mean beta (relabel g h) (D.image g.toEquiv) (g.toEquiv u) = mean beta h D u := by
  change mean beta (relabel g h) (D.image g.toEquiv)
    (TreeGibbsAut.vertexEquiv g D u).val = mean beta h D u
  simpa only [mean, extendFiniteSpin_apply] using
    TreeGibbsAut.spin_expectation_relabel g D beta h u

theorem covariance_relabel {d : ℕ} (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u v : D) :
    covariance beta (relabel g h) (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v) =
      covariance beta h D u v := by
  change covariance beta (relabel g h) (D.image g.toEquiv)
    (TreeGibbsAut.vertexEquiv g D u).val (TreeGibbsAut.vertexEquiv g D v).val = _
  simpa only [covariance, extendFiniteSpin_apply] using
    TreeGibbsAut.spin_covariance_relabel g D beta h u v

theorem response_relabel {d : ℕ} (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u v : D) :
    response beta (relabel g h) (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v) =
      response beta h D u v := by
  rw [response, response, covariance_relabel, mean_relabel]

theorem exists_response_product_of_reroot {d : ℕ} (beta : ℝ)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (u v : D) (g : TreeAut d) (hg : g.toEquiv u = ConnectedHull.root d) :
    ∃ z : ℕ → ℝ, response beta h D u v =
      Real.tanh beta ^ (g.toEquiv v).1.length *
        ∏ i ∈ Finset.range (g.toEquiv v).1.length,
          responseAttenuation (Real.tanh beta) (z i) := by
  have hr : ConnectedHull.root d ∈ D.image g.toEquiv := by
    rw [← hg]
    exact (TreeGibbsAut.vertexEquiv g D u).property
  obtain ⟨z, hz⟩ := exists_root_response_product beta (relabel g h) (hD.image g) hr
    (TreeGibbsAut.vertexEquiv g D v).property
  refine ⟨z, ?_⟩
  rw [← hg] at hz
  change response beta (relabel g h) (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v) = _ at hz
  rw [response_relabel g D beta h u v] at hz
  exact hz

theorem response_mem_Icc_of_reroot {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (u v : D) (g : TreeAut d) (hg : g.toEquiv u = ConnectedHull.root d) :
    response beta h D u v ∈ Set.Icc 0 (Real.tanh beta ^ (g.toEquiv v).1.length) := by
  have hr : ConnectedHull.root d ∈ D.image g.toEquiv := by
    rw [← hg]
    exact (TreeGibbsAut.vertexEquiv g D u).property
  have hb := root_response_mem_Icc hbeta (relabel g h) (hD.image g) hr
    (TreeGibbsAut.vertexEquiv g D v).property
  rw [← hg] at hb
  change response beta (relabel g h) (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v) ∈ Set.Icc 0 _ at hb
  rw [response_relabel g D beta h u v] at hb
  exact hb

theorem lipschitzWith_field_coordinate_of_reroot {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (u v : D) (g : TreeAut d) (hg : g.toEquiv u = ConnectedHull.root d) :
    LipschitzWith
      ⟨Real.tanh beta ^ (g.toEquiv v).1.length,
        pow_nonneg (tanh_nonneg_of_beta_nonneg hbeta) _⟩
      (fun t => field beta (Function.update h v (h v + t)) D u) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro t
    exact (hasDerivAt_field_coordinate beta h u.property v.property t).differentiableAt
  · intro t
    rw [(hasDerivAt_field_coordinate beta h u.property v.property t).deriv]
    have hb := response_mem_Icc_of_reroot hbeta
      (Function.update h v (h v + t)) hD u v g hg
    change |response beta (Function.update h v (h v + t)) D u v| ≤ _
    rw [abs_of_nonneg hb.1]
    exact hb.2

theorem exists_response_product {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) (u v : D) :
    ∃ z : ℕ → ℝ, response beta h D u v =
      Real.tanh beta ^ reducedWordDistance u.1.1 v.1.1 *
        ∏ i ∈ Finset.range (reducedWordDistance u.1.1 v.1.1),
          responseAttenuation (Real.tanh beta) (z i) := by
  obtain ⟨g, hg, hd⟩ := exists_treeAut_to_root_distance u.1
  obtain ⟨z, hz⟩ := exists_response_product_of_reroot beta h hD u v g hg
  exact ⟨z, by simpa only [hd v] using hz⟩

theorem response_mem_Icc {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (u v : D) :
    response beta h D u v ∈ Set.Icc 0 (Real.tanh beta ^ reducedWordDistance u.1.1 v.1.1) := by
  obtain ⟨g, hg, hd⟩ := exists_treeAut_to_root_distance u.1
  simpa only [hd v] using response_mem_Icc_of_reroot hbeta h hD u v g hg

theorem lipschitzWith_field_coordinate {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (u v : D) :
    LipschitzWith
      ⟨Real.tanh beta ^ reducedWordDistance u.1.1 v.1.1,
        pow_nonneg (tanh_nonneg_of_beta_nonneg hbeta) _⟩
      (fun t => field beta (Function.update h v (h v + t)) D u) := by
  obtain ⟨g, hg, hd⟩ := exists_treeAut_to_root_distance u.1
  simpa only [hd v] using lipschitzWith_field_coordinate_of_reroot hbeta h hD u v g hg

end Problem367.TreePathResponse

end

end OAI

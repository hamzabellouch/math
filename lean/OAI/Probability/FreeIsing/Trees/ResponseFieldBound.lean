import OAI.Probability.FreeIsing.Gaussian.TreeResponsePosterior
import OAI.Probability.FreeIsing.Trees.CoordinateResponse

namespace OAI

noncomputable section

namespace Problem367.TreePathResponse

theorem measurable_field {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r : TreeVertex d) : Measurable (fun h => field beta h E r) := by
  classical
  unfold field mean LeafGibbs.expectation GibbsLeaf.energy Real.artanh
  fun_prop

theorem tanh_field {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {E : Finset (TreeVertex d)} {r : TreeVertex d} (hr : r ∈ E) :
    Real.tanh (field beta h E r) = mean beta h E r :=
  Real.tanh_artanh (mean_mem_Ioo beta h hr)

theorem field_uniform_bound {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (h : TreeVertex d → ℝ) (E : Finset (TreeVertex d)) (r : E) :
    |field beta h E r - h r| ≤ (d : ℝ) * beta := by
  have he := finite_tree_gibbs_field_uniform_bound E hb (E.restrict h) r
  unfold field mean
  simp only [extendFiniteSpin_apply E _ r, GibbsLeaf.expectation_eq_fieldMean]
  exact he

theorem field_update_source_noise_bound {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (h : TreeVertex d → ℝ) (E : Finset (TreeVertex d)) (r : E)
    (a z : ℝ) :
    |field beta (Function.update h r (a + z)) E r - z| ≤ |a| + (d : ℝ) * beta := by
  have he := field_uniform_bound hb (Function.update h r (a + z)) E r
  simp only [Function.update_self] at he
  calc
    _ = |(field beta (Function.update h r (a + z)) E r - (a + z)) + a| := by congr 1; ring
    _ ≤ |field beta (Function.update h r (a + z)) E r - (a + z)| + |a| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem covariance_eq_variance_mul_response {d : ℕ} (beta : ℝ)
    (h : TreeVertex d → ℝ) {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hr : r ∈ E) (v : TreeVertex d) :
    covariance beta h E r v = (1 - mean beta h E r ^ 2) * response beta h E r v := by
  unfold response
  field_simp [ne_of_gt (variance_pos beta h hr)]

end Problem367.TreePathResponse

end

end OAI

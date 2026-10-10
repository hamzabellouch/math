import OAI.Probability.FreeIsing.Energy.FiniteLeafCovariance
import OAI.Probability.FreeIsing.Gibbs.LeafMessage

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_expectation_eq_sum_mass
    {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ) (D : Finset (TreeVertex d))
    (f : (D → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) f =
      ∑ eta : D → IsingSpin, GibbsLeaf.mass beta h D (extendFiniteSpin D eta) * f eta := by
  classical
  simp only [LeafGibbs.expectation, GibbsLeaf.mass, GibbsLeaf.weight,
    GibbsLeaf.partition, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro eta heta
  ring

theorem tree_gibbs_expectation_erase
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1)) =
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta
        (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) (extendFiniteSpin (D.erase v) eta)) f := by
  classical
  rw [tree_gibbs_expectation_eq_sum_mass, tree_gibbs_expectation_eq_sum_mass]
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        GibbsLeaf.mass beta h D
          (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) * f z.1 := by
      rw [← (finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta : D → IsingSpin => GibbsLeaf.mass beta h D (extendFiniteSpin D eta) *
          f ((finiteSpinEraseEquiv hv eta).1))]
      simp only [Equiv.apply_symm_apply]
    _ = ∑ eta : D.erase v → IsingSpin,
        (∑ s : IsingSpin, GibbsLeaf.mass beta h D
          (Function.update (extendFiniteSpin (D.erase v) eta) v s)) * f eta := by
      rw [Fintype.sum_prod_type]
      simp only [extendFiniteSpin_eraseEquiv_symm, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro eta heta
      rw [GibbsLeaf.sum_mass_update_eq_cavity beta h hv hp hedges]

theorem tree_gibbs_covariance_erase
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f g : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
      (fun eta => g ((finiteSpinEraseEquiv hv eta).1)) =
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta
        (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) (extendFiniteSpin (D.erase v) eta)) f g := by
  unfold LeafGibbs.covariance
  rw [tree_gibbs_expectation_erase beta h hv hp hedges (fun eta => f eta * g eta),
    tree_gibbs_expectation_erase beta h hv hp hedges f,
    tree_gibbs_expectation_erase beta h hv hp hedges g]

end Problem367

end

end OAI

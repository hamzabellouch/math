import OAI.Probability.FreeIsing.Trees.LeafMarginal
import OAI.Probability.FreeIsing.Trees.RootedProjectivity

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_marginal_of_shared_min
    {d : ℕ} (beta : ℝ) {D E : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hE : ConnectedFinset E) (hDE : D ⊆ E)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length) (h : TreeVertex d → ℝ) :
    ∃ h' : TreeVertex d → ℝ, ∀ f : (D → IsingSpin) → ℝ,
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
        (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDE eta)) =
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h' D (extendFiniteSpin D eta)) f := by
  classical
  revert hE hDE hmin h
  refine Finset.strongInductionOn E ?_
  intro E ih hE hDE hmin h
  by_cases heq : D = E
  · subst E
    exact ⟨h, fun _ => rfl⟩
  · obtain ⟨v, p, hvE, _, hpE, hpne, hEr, hDEr, hedges⟩ :=
      hD.exists_prunable_vertex_of_shared_min hE hDE hr hmin heq
    have hpEr : p ∈ E.erase v := Finset.mem_erase.mpr ⟨hpne, hpE⟩
    have hErE : E.erase v ⊆ E := Finset.erase_subset _ _
    obtain ⟨h', hh'⟩ := ih (E.erase v) (Finset.erase_ssubset hvE) hEr hDEr
      (fun x hx => hmin x (hErE hx))
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
    refine ⟨h', fun f => ?_⟩
    calc
      _ = LeafGibbs.expectation
          (fun eta => GibbsLeaf.energy beta
            (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
            (E.erase v) (extendFiniteSpin (E.erase v) eta))
          (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDEr eta)) := by
        exact tree_gibbs_expectation_erase beta h hvE hpEr hedges
          (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDEr eta))
      _ = _ := hh' f

theorem tree_gibbs_covariance_marginal_of_shared_min
    {d : ℕ} (beta : ℝ) {D E : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hE : ConnectedFinset E) (hDE : D ⊆ E)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length) (h : TreeVertex d → ℝ) :
    ∃ h' : TreeVertex d → ℝ, ∀ f g : (D → IsingSpin) → ℝ,
      LeafGibbs.covariance
        (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
        (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDE eta))
        (fun eta => g (Finset.restrict₂ (π := fun _ => IsingSpin) hDE eta)) =
      LeafGibbs.covariance
        (fun eta => GibbsLeaf.energy beta h' D (extendFiniteSpin D eta)) f g := by
  obtain ⟨h', hh'⟩ := tree_gibbs_marginal_of_shared_min beta hD hE hDE hr hmin h
  refine ⟨h', fun f g => ?_⟩
  unfold LeafGibbs.covariance
  rw [hh' (fun eta => f eta * g eta), hh' f, hh' g]

end Problem367

end

end OAI

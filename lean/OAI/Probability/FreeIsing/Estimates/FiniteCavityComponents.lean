import OAI.Probability.FreeIsing.Cavity.FieldL2Limit
import OAI.Probability.FreeIsing.Estimates.FiniteComponentFields

namespace OAI

noncomputable section

namespace Problem367.CavityFieldLimit

variable {d : ℕ}

lemma finiteSiteField_eq_component_field (beta : ℝ) (D : Finset (TreeVertex d))
    (v : D) (y : TreeVertex d → ℝ) :
    finiteSiteField beta D v y = FiniteIsingSplit.field beta D v y := by
  simp only [finiteSiteField, FiniteIsingSplit.field, FiniteIsingSplit.mean_eq_fieldMean]

theorem finiteCavityField_root_eq_complement {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D)
    (y : TreeVertex d → ℝ) :
    finiteCavityField hbeta D ⟨ConnectedHull.root d, hroot⟩
      ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ y =
    finiteSiteField beta (rootComplementFinset D c)
      ⟨ConnectedHull.root d, rootComplementFinset_root_mem c hroot⟩ y := by
  simp only [finiteCavityField, finiteSiteField_eq_component_field]
  exact congrArg Prod.fst
    (FiniteIsingSplit.cavityFromSites_root_component hbeta D hroot c hc y)

theorem finiteCavityField_child_eq_component {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D)
    (y : TreeVertex d → ℝ) :
    finiteCavityField hbeta D ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩
      ⟨ConnectedHull.root d, hroot⟩ y =
    finiteSiteField beta (rootComponentFinset D c)
      ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩ y := by
  simp only [finiteCavityField, finiteSiteField_eq_component_field]
  have hswap := cavityFromSites_swap (tanh_nonneg_of_beta_nonneg hbeta)
    (Real.tanh_lt_one beta)
    (FiniteIsingSplit.field beta D ⟨ConnectedHull.root d, hroot⟩ y,
      FiniteIsingSplit.field beta D ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ y)
  rw [FiniteIsingSplit.cavityFromSites_root_component hbeta D hroot c hc y] at hswap
  exact congrArg Prod.fst hswap

end Problem367.CavityFieldLimit

end

end OAI

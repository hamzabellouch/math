import OAI.Probability.FreeIsing.Estimates.ComponentGibbsLimit
import OAI.Probability.FreeIsing.Estimates.FiniteCavityComponents

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open CavityFieldLimit PlantedSymmetry

theorem HasFreeIsingLaw.infiniteCavityField_eq_component_of_exhaustion
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ v, ∃ n, v ∈ D n)
    (hroot : ∀ n, ConnectedHull.root d ∈ D n)
    (hc : ∀ n, (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D n) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)
        (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
          ⟨[c], List.IsChain.singleton c⟩ p) := by
  have hfull := hμ.exhaustionCavityField_tendsto_ae hbeta D hD hconn hex
    ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d) hc hroot t
  have hpart := (hμ.rootComponent_gibbsField_limit hbeta t c D hD hconn hex hroot hc).1
  filter_upwards [hfull, hpart] with p hp hpart
  have hseq (n : ℕ) :
      finiteCavityField hbeta (D n) ⟨⟨[c], List.IsChain.singleton c⟩, hc n⟩
        ⟨ConnectedHull.root d, hroot n⟩ (observation t p) =
      Real.artanh (FiniteIsingSplit.mean beta (rootComponentFinset (D n) c)
        ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c (hc n)⟩
        (observation t p)) := by
    rw [finiteCavityField_child_eq_component hbeta (D n) (hroot n) c (hc n)]
    exact finiteSiteField_eq_component_field _ _ _ _
  exact tendsto_nhds_unique ((tendsto_congr hseq).mp hp) hpart

theorem HasFreeIsingLaw.infiniteCavityField_eq_component
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)
        (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
          ⟨[c], List.IsChain.singleton c⟩ p) := by
  let r : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  apply hμ.infiniteCavityField_eq_component_of_exhaustion hbeta t c
    (connectedExhaustion r) (connectedExhaustion_monotone r)
    (connectedExhaustion_connected r)
    (fun v => (eventually_mem_connectedExhaustion r v).exists)
    _ (mem_connectedExhaustion r)
  intro n
  classical
  simp [connectedExhaustion, ConnectedHull.hull]

end Problem367

end

end OAI

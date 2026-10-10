import OAI.Probability.FreeIsing.Estimates.FiniteComponentGeometry
import OAI.Probability.FreeIsing.Estimates.FiniteIsingSplit
import OAI.Probability.FreeIsing.Posterior.ComponentPosteriorStationarity
import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorLimit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

def rootComponentIndices {d : ℕ} (D : Finset (TreeVertex d)) (c : Fin d) :
    Finset (ComponentIndex c) := by
  classical
  exact D.preimage componentIndexVertex (componentIndexVertex_injective c).injOn

@[simp] theorem mem_rootComponentIndices {d : ℕ} {D : Finset (TreeVertex d)}
    {c : Fin d} {u : ComponentIndex c} :
    u ∈ rootComponentIndices D c ↔ componentIndexVertex u ∈ D := by
  classical
  exact Finset.mem_preimage

theorem rootComponentIndices_monotone {d : ℕ} (c : Fin d) :
    Monotone (fun D : Finset (TreeVertex d) => rootComponentIndices D c) := by
  intro D E hDE u hu
  exact mem_rootComponentIndices.mpr (hDE (mem_rootComponentIndices.mp hu))

theorem selectedObservationField_rootComponentIndices {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (D : Finset (TreeVertex d)) (c : Fin d) :
    selectedObservationField F (fun u : rootComponentIndices D c => componentIndexVertex u.1) =
      selectedObservationField F (fun v : rootComponentFinset D c => v.1) := by
  apply selectedObservationField_eq_of_range_eq
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨componentIndexVertex u.1, mem_rootComponentFinset.mpr
      ⟨mem_rootComponentIndices.mp u.2, ?_⟩⟩, rfl⟩
    apply (singleton_prefix_iff_cons c _).mpr
    exact ⟨u.1.2.1, rfl⟩
  · rintro ⟨v, rfl⟩
    have hv := mem_rootComponentFinset.mp v.2
    obtain ⟨u, hu⟩ := mem_range_componentIndexVertex.mpr
      ((singleton_prefix_iff_cons c v.1).mp hv.2)
    refine ⟨⟨u, mem_rootComponentIndices.mpr ?_⟩, hu⟩
    exact hu.symm ▸ hv.1

theorem HasFreeIsingLaw.rootComponent_gibbsMean_eq_selectedPosterior
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (hroot : ConnectedHull.root d ∈ D) (c : Fin d)
    (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) (t : ℝ≥0) :
    (fun p => FiniteIsingSplit.mean β (rootComponentFinset D c)
      ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
      (PlantedSymmetry.observation t p)) =ᵐ[μ.prod
        (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)]
    selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
      (fun s z => (t : ℝ) * spinSign s + z)
      (fun u : rootComponentIndices D c => componentIndexVertex u.1)
      ⟨[c], List.IsChain.singleton c⟩ := by
  let E := rootComponentFinset D c
  let r : E := ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
  have hce := hμ.finiteObservation_condExp E
    (rootComponentFinset_connected hD hroot c hc) t (fun eta => spinSign (eta r))
  simp only [selectedPosterior, selectedObservationField_rootComponentIndices]
  have hsigma : selectedObservationField (fun s z => (t : ℝ) * spinSign s + z)
      (fun v : E => v.1) = MeasurableSpace.comap (finiteObservation E t) inferInstance := rfl
  rw [hsigma]
  simp only [FiniteIsingSplit.mean_eq_fieldMean]
  convert hce.symm using 1 <;> rfl

theorem HasFreeIsingLaw.rootComponent_gibbsField_limit
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (t : ℝ≥0) (c : Fin d)
    (D : ℕ → Finset (TreeVertex d)) (hmono : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ v, ∃ n, v ∈ D n)
    (hroot : ∀ n, ConnectedHull.root d ∈ D n)
    (hc : ∀ n, (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D n) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let H : ℕ → ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
      fun n p => Real.artanh (FiniteIsingSplit.mean β (rootComponentFinset (D n) c)
        ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c (hc n)⟩
        (PlantedSymmetry.observation t p))
    let Z := fun p => Real.artanh (selectedPosterior ρ
      (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
        ⟨[c], List.IsChain.singleton c⟩ p)
    (∀ᵐ p ∂ρ, Tendsto (fun n => H n p) atTop (𝓝 (Z p))) ∧
      Tendsto (fun n => ∫ p, (H n p - Z p) ^ 2 ∂ρ) atTop (𝓝 0) := by
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let r : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  let I := fun n => rootComponentIndices (D n) c
  have hI : Monotone I := fun _ _ hnm => rootComponentIndices_monotone c (hmono hnm)
  have hexI : ∀ u : ComponentIndex c, ∃ n, u ∈ I n := by
    intro u
    obtain ⟨n, hn⟩ := hex (componentIndexVertex u)
    exact ⟨n, mem_rootComponentIndices.mpr hn⟩
  have hrI : ∀ n, r ∈ Set.range (fun u : I n => componentIndexVertex u.1) := by
    intro n
    let u : ComponentIndex c := ⟨0, ⟨[], rfl, List.IsChain.singleton c⟩⟩
    exact ⟨⟨u, mem_rootComponentIndices.mpr (hc n)⟩, rfl⟩
  have hlim := hμ.selected_gaussian_posterior_field_limit hβ t
    (componentIndexVertex (c := c)) r I hI hexI hrI
  have hce (n : ℕ) := hμ.rootComponent_gibbsMean_eq_selectedPosterior
    (D n) (hconn n) (hroot n) c (hc n) t
  constructor
  · filter_upwards [hlim.1, ae_all_iff.mpr hce] with p hp hce
    convert hp using 1
    funext n
    exact congrArg Real.artanh (hce n)
  · convert hlim.2 using 1
    funext n
    apply integral_congr_ae
    filter_upwards [hce n] with p hp
    rw [hp]

end Problem367

end

end OAI

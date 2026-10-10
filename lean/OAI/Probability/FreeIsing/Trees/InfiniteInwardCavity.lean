import OAI.Probability.FreeIsing.Trees.InfiniteConeCavity
import OAI.Probability.FreeIsing.Trees.InwardCutFields

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367
open PlantedSymmetry CavityFieldLimit PathSideBranches

theorem HasFreeIsingLaw.infiniteCavityField_eq_complement_posterior
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∀ᵐ z ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta (parentVertex r) r (observation t z) =
        regionGaussianField μ t (cone r)ᶜ (parentVertex r) z := by
  obtain ⟨g, c, hr0, hpc, hcone⟩ := exists_reroot_cone_complement r hr
  have hp' : g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩ = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hpc]
  have hr' : g.toEquiv.symm (ConnectedHull.root d) = r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hr0]
  have hregion : Set.range
      (fun i : ComponentIndex c => g.toEquiv.symm (componentIndexVertex i)) =
      Set.range (Subtype.val : ((cone r)ᶜ : Set (TreeVertex d)) → TreeVertex d) := by
    ext u
    rw [Subtype.range_coe_subtype]
    constructor
    · rintro ⟨i, rfl⟩
      apply (hcone _).mpr
      rw [Equiv.apply_symm_apply]
      apply (singleton_prefix_iff_cons c _).mpr
      exact ⟨i.2.1, rfl⟩
    · intro hu
      have hbranch := (singleton_prefix_iff_cons c (g.toEquiv u)).mp ((hcone u).mp hu)
      obtain ⟨i, hi⟩ := mem_range_componentIndexVertex.mpr hbranch
      refine ⟨i, ?_⟩
      change g.toEquiv.symm (componentIndexVertex i) = u
      rw [hi, Equiv.symm_apply_apply]
  have hfield := selectedObservationField_eq_of_range_eq
    (fun (s : IsingSpin) (x : ℝ) => (t : ℝ) * spinSign s + x) hregion
  simpa only [hp', hr', regionGaussianField, selectedPosterior, hfield] using
    hμ.infiniteCavityField_eq_relabelled_component hbeta t g c

theorem HasFreeIsingLaw.infiniteCavityField_path_eq_inward_posterior
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {i : ℕ} (hi : i < v.1.length) :
    ∀ᵐ z ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta (ConnectedHull.takeVertex v i)
        (ConnectedHull.takeVertex v (i + 1)) (observation t z) =
      inwardGaussianField μ t v i z := by
  have hr : (ConnectedHull.takeVertex v (i + 1)).1 ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp only [ConnectedHull.takeVertex, List.length_take, List.length_nil] at hl
    omega
  simpa only [parent_takeVertex_succ v hi, inwardGaussianField] using
    hμ.infiniteCavityField_eq_complement_posterior hbeta t
      (ConnectedHull.takeVertex v (i + 1)) hr

end Problem367

end

end OAI

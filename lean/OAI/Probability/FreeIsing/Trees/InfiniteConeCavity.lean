import OAI.Probability.FreeIsing.Factors.InfiniteCavityNaturality
import OAI.Probability.FreeIsing.Trees.PathSideReroot

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry CavityFieldLimit PathSideBranches

theorem HasFreeIsingLaw.infiniteCavityField_eq_cone_posterior
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hβ r (parentVertex r) (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z)
        (Subtype.val : cone r → TreeVertex d) r p) := by
  obtain ⟨g, c, hp, hc, hcone⟩ := exists_reroot_cone r hr
  have hr' : g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩ = r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hc]
  have hp' : g.toEquiv.symm (ConnectedHull.root d) = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hp]
  have hregion : Set.range
      (fun i : ComponentIndex c => g.toEquiv.symm (componentIndexVertex i)) =
      Set.range (Subtype.val : cone r → TreeVertex d) := by
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
    (fun (s : IsingSpin) (z : ℝ) => (t : ℝ) * spinSign s + z) hregion
  simpa only [hr', hp', selectedPosterior, hfield] using
    hμ.infiniteCavityField_eq_relabelled_component hβ t g c

theorem HasFreeIsingLaw.infiniteCavityField_path_eq_forward_posterior
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β)
    (t : ℝ≥0) (v : TreeVertex d) (k : ℕ) (hk : k < v.1.length) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hβ (ConnectedHull.takeVertex v (k + 1))
        (ConnectedHull.takeVertex v k) (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z)
        (Subtype.val : cone (ConnectedHull.takeVertex v (k + 1)) → TreeVertex d)
        (ConnectedHull.takeVertex v (k + 1)) p) := by
  have hr : (ConnectedHull.takeVertex v (k + 1)).1 ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [ConnectedHull.takeVertex, List.length_take, List.length_nil] at hlen
    omega
  have hp : parentVertex (ConnectedHull.takeVertex v (k + 1)) =
      ConnectedHull.takeVertex v k := by
    apply Subtype.ext
    simp only [parentVertex, ConnectedHull.takeVertex,
      List.take_succ_eq_append_getElem hk, List.dropLast_concat]
  simpa only [hp] using hμ.infiniteCavityField_eq_cone_posterior hβ t
    (ConnectedHull.takeVertex v (k + 1)) hr

end Problem367

end

end OAI

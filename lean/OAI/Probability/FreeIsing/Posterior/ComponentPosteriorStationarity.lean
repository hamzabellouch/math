import OAI.Probability.FreeIsing.Conditioning.ComponentInformation
import OAI.Probability.FreeIsing.Estimates.ColorAutomorphisms
import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorStationarity
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem mem_range_componentIndexVertex {d : ℕ} {c : Fin d} {v : TreeVertex d} :
    v ∈ Set.range (componentIndexVertex (c := c)) ↔ ∃ w, v.1 = c :: w := by
  constructor
  · rintro ⟨⟨n, w⟩, rfl⟩
    exact ⟨w.1, rfl⟩
  · rintro ⟨w, hw⟩
    have hchain : (c :: w).IsChain (fun a b : Fin d => a ≠ b) := by
      rw [← hw]
      exact v.2
    refine ⟨⟨w.length, ⟨w, rfl, hchain⟩⟩, ?_⟩
    exact Subtype.ext hw.symm

theorem range_componentIndexVertex_colorPerm {d : ℕ} (e : Equiv.Perm (Fin d)) (c : Fin d) :
    Set.range (fun u : ComponentIndex c => (colorPermAut e).toEquiv.symm
      (componentIndexVertex u)) = Set.range (componentIndexVertex (c := e.symm c)) := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    apply mem_range_componentIndexVertex.mpr
    refine ⟨u.2.1.map e.symm, ?_⟩
    rfl
  · intro hv
    obtain ⟨w, hw⟩ := mem_range_componentIndexVertex.mp hv
    have hmem : (colorPermAut e).toEquiv v ∈ Set.range (componentIndexVertex (c := c)) := by
      apply mem_range_componentIndexVertex.mpr
      refine ⟨w.map e, ?_⟩
      simp [hw]
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, ?_⟩
    change (colorPermAut e).toEquiv.symm (componentIndexVertex u) = v
    rw [hu, Equiv.symm_apply_apply]

theorem componentPosterior_identDistrib {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c a : Fin d) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (componentIndexVertex (c := c)) ⟨[c], List.IsChain.singleton c⟩)
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (componentIndexVertex (c := a)) ⟨[a], List.IsChain.singleton a⟩)
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  let e : Equiv.Perm (Fin d) := Equiv.swap c a
  have hmap : e.symm c = a := by simp [e]
  apply selectedPosterior_identDistrib_of_range_relabel hmu nu hF
    (componentIndexVertex (c := c)) (componentIndexVertex (c := a))
    ⟨[c], List.IsChain.singleton c⟩ ⟨[a], List.IsChain.singleton a⟩ (colorPermAut e)
  · rw [← hmap]
    exact range_componentIndexVertex_colorPerm e c
  · apply Subtype.ext
    change [e.symm c] = [a]
    rw [hmap]

def childComponentIndexVertex {d : ℕ} (c a : Fin d) (u : ComponentIndex a) : TreeVertex d :=
  prefixFlip c (componentIndexVertex u)

theorem childComponentIndexVertex_val {d : ℕ} {c a : Fin d} (hca : c ≠ a)
    (u : ComponentIndex a) : (childComponentIndexVertex c a u).1 = c :: a :: u.2.1 := by
  simp [childComponentIndexVertex, prefixFlip, prefixFlipWord, componentIndexVertex, componentVertex, hca]

theorem childComponentPosterior_identDistrib {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c a : Fin d) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (childComponentIndexVertex c a) (prefixFlip c ⟨[a], List.IsChain.singleton a⟩))
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (componentIndexVertex (c := c)) ⟨[c], List.IsChain.singleton c⟩)
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  have h := selectedPosterior_identDistrib_relabel hmu nu hF
    (componentIndexVertex (c := a)) ⟨[a], List.IsChain.singleton a⟩ (prefixTreeAut c)
  exact h.symm.trans (componentPosterior_identDistrib hmu nu hF a c)

end Problem367

end

end OAI

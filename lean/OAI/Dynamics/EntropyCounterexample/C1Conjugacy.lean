import OAI.Dynamics.EntropyCounterexample.C1Coordinates
import OAI.Dynamics.EntropyCounterexample.Conjugacy

namespace OAI

noncomputable section

namespace Problem340

theorem HasLocalC1Extension.comp
    {X Y E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {eX : X → E} {eY : Y → F} {f : X → Y} {g : Y → G}
    (hg : HasLocalC1Extension eY g)
    (hf : HasLocalC1Extension eX (eY ∘ f)) :
    HasLocalC1Extension eX (g ∘ f) := by
  intro x
  obtain ⟨U, hU, hxU, F, hF, hFe⟩ := hf x
  simp only [Function.comp_apply] at hFe
  obtain ⟨V, hV, hfxV, G, hG, hGe⟩ := hg (f x)
  refine ⟨U ∩ F ⁻¹' V, hF.continuousOn.isOpen_inter_preimage hU hV, ?_,
    G ∘ F, hG.comp_inter hF, ?_⟩
  · refine ⟨hxU, ?_⟩
    change F (eX x) ∈ V
    rw [← hFe x hxU]
    exact hfxV
  · intro y hy
    change g (f y) = G (F (eX y))
    rw [hGe (f y) (by rw [hFe y hy.1]; exact hy.2), hFe y hy.1]

theorem HasLocalC1Extension.conjugateMap
    {X Y E F : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {eX : X → E} {eY : Y → F} (e : X ≃ₜ Y) {f : X → X}
    (hforward : HasLocalC1Extension eX (eY ∘ e))
    (hinverse : HasLocalC1Extension eY (eX ∘ e.symm))
    (hf : HasLocalC1Extension eX (eX ∘ f)) :
    HasLocalC1Extension eY (eY ∘ conjugateMap e f) :=
  (hforward.comp hf).comp hinverse

theorem isC1SelfMap_conjugateMap_of_embeddings
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} {eX : X → E} (e : X ≃ₜ CounterexampleManifold q) {f : X → X}
    (hforward : HasLocalC1Extension eX (standardEmbedding q ∘ e))
    (hinverse : HasLocalC1Extension (standardEmbedding q) (eX ∘ e.symm))
    (hf : HasLocalC1Extension eX (eX ∘ f)) :
    IsC1SelfMap q (conjugateMap e f) :=
  isC1SelfMap_iff_hasLocalC1Extension.mpr
    (HasLocalC1Extension.conjugateMap e hforward hinverse hf)

end Problem340

end

end OAI

import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

open Topology

namespace Problem340

theorem isEmbedding_standardEmbedding (q : ℕ) :
    IsEmbedding (standardEmbedding q) := by
  exact IsEmbedding.subtypeVal.prodMap
    (IsEmbedding.piMap fun _ => IsEmbedding.subtypeVal)

@[continuity, fun_prop]
theorem continuous_standardEmbedding (q : ℕ) : Continuous (standardEmbedding q) :=
  (isEmbedding_standardEmbedding q).continuous

theorem standardEmbedding_injective (q : ℕ) : Function.Injective (standardEmbedding q) :=
  (isEmbedding_standardEmbedding q).injective

theorem continuous_iff_standardEmbedding {X : Type*} [TopologicalSpace X]
    (q : ℕ) (f : X → CounterexampleManifold q) :
    Continuous f ↔ Continuous (standardEmbedding q ∘ f) :=
  (isEmbedding_standardEmbedding q).continuous_iff

theorem isC1SelfMap_of_contDiff {q : ℕ}
    (f : CounterexampleManifold q → CounterexampleManifold q)
    (F : CounterexampleAmbient q → CounterexampleAmbient q)
    (hF : ContDiff ℝ 1 F)
    (hcomm : ∀ y, standardEmbedding q (f y) = F (standardEmbedding q y)) :
    IsC1SelfMap q f := by
  refine ⟨?_, ?_⟩
  · apply (continuous_iff_standardEmbedding q f).2
    have heq : standardEmbedding q ∘ f = F ∘ standardEmbedding q := funext hcomm
    rw [heq]
    exact hF.continuous.comp (continuous_standardEmbedding q)
  · intro x
    exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, F, hF.contDiffOn,
      fun y _ => hcomm y⟩

theorem continuous_of_local_contDiff_extension {q : ℕ}
    (f : CounterexampleManifold q → CounterexampleManifold q)
    (hlocal : ∀ x : CounterexampleManifold q,
      ∃ U : Set (CounterexampleAmbient q),
        IsOpen U ∧ standardEmbedding q x ∈ U ∧
          ∃ F : CounterexampleAmbient q → CounterexampleAmbient q,
            ContDiffOn ℝ 1 F U ∧
              ∀ y : CounterexampleManifold q,
                standardEmbedding q y ∈ U →
                  standardEmbedding q (f y) = F (standardEmbedding q y)) :
    Continuous f := by
  apply (continuous_iff_standardEmbedding q f).2
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hxU, F, hF, hcomm⟩ := hlocal x
  have hcont : ContinuousAt (F ∘ standardEmbedding q) x :=
    (hF.contDiffAt (hU.mem_nhds hxU)).continuousAt.comp
      (continuous_standardEmbedding q).continuousAt
  apply hcont.congr_of_eventuallyEq
  filter_upwards [(continuous_standardEmbedding q).continuousAt.preimage_mem_nhds
    (hU.mem_nhds hxU)] with y hy
  exact hcomm y hy

theorem IsC1SelfMap.comp {q : ℕ}
    {f g : CounterexampleManifold q → CounterexampleManifold q}
    (hg : IsC1SelfMap q g) (hf : IsC1SelfMap q f) :
    IsC1SelfMap q (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro x
  obtain ⟨U, hU, hxU, F, hF, hcommF⟩ := hf.2 x
  obtain ⟨V, hV, hfxV, G, hG, hcommG⟩ := hg.2 (f x)
  refine ⟨U ∩ F ⁻¹' V, hF.continuousOn.isOpen_inter_preimage hU hV, ?_,
    G ∘ F, hG.comp_inter hF, ?_⟩
  · exact ⟨hxU, by simpa only [Set.mem_preimage, ← hcommF x hxU] using hfxV⟩
  · intro y hy
    change standardEmbedding q (g (f y)) = G (F (standardEmbedding q y))
    rw [hcommG (f y), hcommF y hy.1]
    simpa only [hcommF y hy.1, Set.mem_preimage] using hy.2

theorem isC1SelfMap_id (q : ℕ) :
    IsC1SelfMap q (id : CounterexampleManifold q → CounterexampleManifold q) :=
  isC1SelfMap_of_contDiff id id contDiff_id (fun _ => rfl)

theorem isC1SelfMap_const {q : ℕ} (c : CounterexampleManifold q) :
    IsC1SelfMap q (fun _ : CounterexampleManifold q => c) :=
  isC1SelfMap_of_contDiff (fun _ => c) (fun _ => standardEmbedding q c)
    contDiff_const (fun _ => rfl)

theorem IsC1SelfMap.iterate {q : ℕ}
    {f : CounterexampleManifold q → CounterexampleManifold q}
    (hf : IsC1SelfMap q f) (n : ℕ) : IsC1SelfMap q (f^[n]) := by
  induction n with
  | zero => exact isC1SelfMap_id q
  | succ n hn =>
      rw [Function.iterate_succ']
      exact hf.comp hn

end Problem340

end

end OAI

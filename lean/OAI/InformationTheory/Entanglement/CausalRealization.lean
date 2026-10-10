import OAI.InformationTheory.Entanglement.CausalIndependence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Function
open scoped MeasureTheory ProbabilityTheory unitInterval
namespace SecretKey
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
variable (role : ℕ → TapeRole) (pub : Set ℕ) (x₀ : X)

def visibleKernel (κ : (k : ℕ) → Kernel (Fin k → X) X) (k : ℕ) : Kernel (Fin k→X) X :=
  (κ k).comap (visiblePrefix role pub x₀ (role k) k)
    (visiblePrefix_measurable role pub x₀ (role k) k)
instance visibleKernel_markov (κ : (k : ℕ) → Kernel (Fin k → X) X)
    [∀ k, IsMarkovKernel (κ k)] (k : ℕ) : IsMarkovKernel (visibleKernel role pub x₀ κ k) := by
  unfold visibleKernel
  infer_instance

theorem causal_history_realization (hsource : ∀ k, role k=.source → k∈pub)
    (κ : (k : ℕ) → Kernel (Fin k → X) X) [∀ k, IsMarkovKernel (κ k)]
    (ν : Measure (ℕ→X)) [IsProbabilityMeasure ν]
    (hν : ∀ k, ν.map (fun x => (recordPrefix k x,x k))=
      ν.map (recordPrefix k) ⊗ₘ visibleKernel role pub x₀ κ k) :
    ∃ g : (k : ℕ) → (Fin k → X) → I → X,
      (∀ k, Measurable (uncurry (g k))) ∧
      ν=uniformTapesLaw.map (sampledHistory (causalSampler role pub x₀ g)) ∧
      ∃ hT : Measurable (completeCausalPublic role pub x₀ g),
        CondIndep ((inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
          (roleInfo role .alice ⊔ (inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
          (roleInfo role .bob ⊔ (inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
          hT.comap_le uniformTapesLaw := by
  have hs (k : ℕ) := (κ k).exists_measurable_map_eq_unitInterval
  choose g hg hmap using hs
  refine ⟨g,hg,?_,completeCausalPublic_measurable role pub x₀ g hg,
    causal_complete_independence role pub x₀ g hg hsource κ hmap⟩
  apply sampled_full_history_law _ (causalSampler_measurable role pub x₀ g hg)
    (visibleKernel role pub x₀ κ) _ ν hν
  intro k s
  exact hmap k (visiblePrefix role pub x₀ (role k) k s)

omit [StandardBorelSpace X] [Nonempty X] in
theorem causal_terminal_values_independent
    (g : (k : ℕ) → (Fin k → X) → I → X)
    (hg : ∀ k, Measurable (uncurry (g k)))
    (hsource : ∀ k, role k=.source → k∈pub)
    (κ : (k : ℕ) → Kernel (Fin k → X) X) [∀ k, IsMarkovKernel (κ k)]
    (hmap : ∀ k s, volume.map (g k s)=κ k s)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (ℕ→X) → α) (q : (ℕ→X) → β) (hf : Measurable f) (hq : Measurable q) :
    CondIndepFun ((inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
      (completeCausalPublic_measurable role pub x₀ g hg).comap_le
      (f ∘ completeCausalView role pub x₀ g .alice)
      (q ∘ completeCausalView role pub x₀ g .bob) uniformTapesLaw := by
  have hi := causal_complete_independence role pub x₀ g hg hsource κ hmap
  rw [condIndepFun_iff_condIndep]
  apply condIndep_of_condIndep_of_le_right (condIndep_of_condIndep_of_le_left hi ?_) ?_
  · have hf' := (hf.comp (completeCausalView_local role pub x₀ g hg .alice)).comap_le
    simpa only [← completeCausalPublic_information] using hf'
  · have hq' := (hq.comp (completeCausalView_local role pub x₀ g hg .bob)).comap_le
    simpa only [← completeCausalPublic_information] using hq'

end SecretKey

end

end OAI

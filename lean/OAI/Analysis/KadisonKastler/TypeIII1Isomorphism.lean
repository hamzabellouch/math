import OAI.Analysis.KadisonKastler.PublishedModularCoreType
import OAI.Analysis.KadisonKastler.PublishedCoreIsomorphism
import OAI.Analysis.KadisonKastler.SemifiniteIsomorphism

namespace OAI

/-! # Representation independence of the type III₁ conclusion -/

namespace KadisonKastler

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

theorem TypeIII1Factor.of_starAlgEquiv (hM : TypeIII1Factor M)
    (hCore : PublishedModularCoreIsomorphism.{u})
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hc : DenseRange (algebraVectorMap M Ω))
    (hs : Function.Injective (algebraVectorMap M Ω))
    (m : ModularSpectralResolution M Ω) : TypeIII1Factor N := by
  have hm : ∀ t x, x ∈ M → unitaryConj (m.group t) x ∈ M := by
    intro t x hx
    change unitaryConj (m.group t) x ∈ (M : Set (H →L[ℂ] H))
    rw [← m.normalizes t]
    exact Set.mem_image_of_mem _ hx
  refine { hM.toTypeIIIFactor.of_starAlgEquiv e with core_type := ?_ }
  intro ξ hξ hcN hsN V hV hn hmod
  obtain ⟨f⟩ := hCore H K M N e Ω ξ hΩ hξ hc hs hcN hsN
    m.group m.continuous hm m.isModular V hV hn hmod
  exact (hM.core_type Ω hΩ hc hs m.group m.continuous hm m.isModular).of_starAlgEquiv f

end

end KadisonKastler

end OAI

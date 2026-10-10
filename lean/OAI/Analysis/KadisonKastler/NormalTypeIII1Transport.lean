import OAI.Analysis.KadisonKastler.NormalCoreIsomorphism
import OAI.Analysis.KadisonKastler.TypeIII1Isomorphism
import OAI.Analysis.KadisonKastler.NormalEquivOnto

namespace OAI

/-! # Type III₁ transport for specified normal representation changes -/

namespace KadisonKastler

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

theorem TypeIII1Factor.of_normalStarAlgEquiv (hM : TypeIII1Factor M)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (he : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp e.toStarAlgHom))
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hc : DenseRange (algebraVectorMap M Ω))
    (hs : Function.Injective (algebraVectorMap M Ω)) (m : ModularSpectralResolution M Ω) :
    TypeIII1Factor N := by
  have hm : ∀ t x, x ∈ M → unitaryConj (m.group t) x ∈ M := by
    intro t x hx
    change unitaryConj (m.group t) x ∈ (M : Set (H →L[ℂ] H))
    rw [← m.normalizes t]
    exact Set.mem_image_of_mem _ hx
  refine { hM.toTypeIIIFactor.of_starAlgEquiv e with core_type := ?_ }
  intro ξ hξ hcN hsN V hV hn hmod
  obtain ⟨f⟩ := modularCore_equiv_of_normal e he Ω ξ hc hcN hs hsN
    m.group m.continuous hm m.isModular V hV hn hmod
  exact (hM.core_type Ω hΩ hc hs m.group m.continuous hm m.isModular).of_starAlgEquiv f

theorem TypeIII1Factor.of_normalStarAlgEquiv_symm (hN : TypeIII1Factor N)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (he : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp e.toStarAlgHom))
    (ξ : K) (hξ : ‖ξ‖ = 1) (hc : DenseRange (algebraVectorMap N ξ))
    (hs : Function.Injective (algebraVectorMap N ξ)) (m : ModularSpectralResolution N ξ) :
    TypeIII1Factor M := by
  have hm : ∀ t x, x ∈ N → unitaryConj (m.group t) x ∈ N := by
    intro t x hx
    change unitaryConj (m.group t) x ∈ (N : Set (K →L[ℂ] K))
    rw [← m.normalizes t]
    exact Set.mem_image_of_mem _ hx
  refine { hN.toTypeIIIFactor.of_starAlgEquiv e.symm with core_type := ?_ }
  intro Ω hΩ hcM hsM U hU hn hmod
  obtain ⟨f⟩ := modularCore_equiv_of_normal e he Ω ξ hcM hc hsM hs
    U hU hn hmod m.group m.continuous hm m.isModular
  exact (hN.core_type ξ hξ hc hs m.group m.continuous hm m.isModular).of_starAlgEquiv f.symm

/-- Pull the type conclusion back through a faithful normal representation
with a specified concrete range. -/
theorem TypeIII1Factor.of_normalHom (hN : TypeIII1Factor N)
    (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (hfaith : Function.Injective φ)
    (hφ : BoundedWeakNormal M φ) (hmem : ∀ a, φ a ∈ N)
    (hrange : generatedVonNeumannAlgebra φ.range = N)
    (ξ : K) (hξ : ‖ξ‖ = 1) (hc : DenseRange (algebraVectorMap N ξ))
    (hs : Function.Injective (algebraVectorMap N ξ)) (m : ModularSpectralResolution N ξ) :
    TypeIII1Factor M :=
  hN.of_normalStarAlgEquiv_symm (normalEquivOnto M N φ hfaith hφ hmem hrange)
    (normalEquivOnto_boundedWeakNormal M N φ hfaith hφ hmem hrange) ξ hξ hc hs m

end

end KadisonKastler

end OAI

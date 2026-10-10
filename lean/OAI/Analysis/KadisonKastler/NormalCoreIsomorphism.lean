import OAI.Analysis.KadisonKastler.NormalSpatialImplementation
import OAI.Analysis.KadisonKastler.SpatialVectorTransport
import OAI.Analysis.KadisonKastler.StatePreservingCoreIsomorphism
import OAI.Analysis.KadisonKastler.SameSpaceCoreIsomorphism

namespace OAI

/-! # Core independence under the normal representation change used in the application -/

namespace KadisonKastler

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

theorem modularCore_equiv_of_normal
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))
    (Ω : H) (ξ : K)
    (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap N ξ))
    (hΩs : Function.Injective (algebraVectorMap M Ω))
    (hξs : Function.Injective (algebraVectorMap N ξ))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M) (hKU : IsModularStateGroup M Ω U)
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hnV : ∀ t a, a ∈ N → unitaryConj (V t) a ∈ N) (hKV : IsModularStateGroup N ξ V) :
    Nonempty (Algebra (regularCoreAlgebra U hU M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra V hV N)) := by
  obtain ⟨W, hW⟩ := exists_spatial_of_normal_cyclic_separating θ hθ Ω ξ hΩc hξc hΩs hξs
  let η := W.symm ξ
  have hηc : DenseRange (algebraVectorMap M η) := spatialVectorTransport_cyclic θ W hW ξ hξc
  have hηs : Function.Injective (algebraVectorMap M η) :=
    spatialVectorTransport_separating θ W hW ξ hξs
  obtain ⟨_, mη⟩ := (publishedModularSpectralResolution H M η hηc hηs).some
  have hnη : ∀ t a, a ∈ M → unitaryConj (mη.group t) a ∈ M := by
    intro t a ha
    change unitaryConj (mη.group t) a ∈ (M : Set (H →L[ℂ] H))
    rw [← mη.normalizes t]
    exact Set.mem_image_of_mem _ ha
  obtain ⟨e₁⟩ := modularCore_equiv_of_two_states M Ω η hΩc hηc hΩs hηs
    U hU hnU hKU mη.group mη.continuous hnη mη.isModular
  obtain ⟨e₂⟩ := modularCore_equiv_of_statePreserving θ η ξ hηc hξc hηs hξs
    (spatialVectorTransport_state θ W hW ξ)
    mη.group mη.continuous hnη mη.isModular V hV hnV hKV
  exact ⟨e₁.trans e₂⟩

end

end KadisonKastler

end OAI

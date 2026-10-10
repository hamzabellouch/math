import OAI.Analysis.KadisonKastler.NormalTwoStateIntertwining
import OAI.Analysis.KadisonKastler.ModularSpectralConstruction

namespace OAI

/-! # Spatial implementation between cyclic separating normal representations

Only the explicitly supplied bounded weak continuity of the representation
change is used. The two diagonal vector states need not agree.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- The spatial map is constructed from the two-state matrix algebra and its modular conjugation. -/
theorem exists_spatial_of_normal_cyclic_separating
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))
    (Ω : H) (ξ : K)
    (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap N ξ))
    (hΩs : Function.Injective (algebraVectorMap M Ω))
    (hξs : Function.Injective (algebraVectorMap N ξ)) :
    ∃ W : H ≃ₗᵢ[ℂ] K, ∀ (a : Algebra M) (x : H), W (a.val x) = (θ a).val (W x) := by
  have hc := normalTwoStateAlgebra_cyclic θ hθ Ω ξ hΩc hξc
  have hs := normalTwoStateAlgebra_separating θ hθ Ω ξ hΩs hξs
  obtain ⟨d, _⟩ := (publishedModularSpectralResolution (TwoStateMatrixHilbert H K)
    (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ) hc hs).some
  exact ⟨normalTwoStateUnitary θ hθ Ω ξ hc d,
    normalTwoStateUnitary_intertwines θ hθ Ω ξ hc d⟩

end

end KadisonKastler

end OAI

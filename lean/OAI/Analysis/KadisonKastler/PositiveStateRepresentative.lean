import OAI.Analysis.KadisonKastler.TwoStatePositiveCorner
import OAI.Analysis.KadisonKastler.TwoStatePositiveTransport
import OAI.Analysis.KadisonKastler.SpatialVectorTransport
import OAI.Analysis.KadisonKastler.TypeIIICyclicState

namespace OAI

/-! # Positive representatives of the faithful vector states used by stability

The positive off-diagonal matrix vector gives a representative in the
reference cone. Its partial isometry between the two corners preserves the
original algebra action and hence the vector functional.
-/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveRepresentativeReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem exists_positive_representative_of_cyclic
    (Ω ξ : H)
    (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
    (hΩs : Function.Injective (algebraVectorMap M Ω))
    (hξs : Function.Injective (algebraVectorMap M ξ))
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H) :
    ∃ η : H, η ∈ canonicalModularPositiveCone J Ω hΩs hΩc ∧
      ‖η‖=‖ξ‖ ∧ Function.Injective (algebraVectorMap M η) ∧
      DenseRange (algebraVectorMap M η) ∧
      vectorFunctional (M := M) η=vectorFunctional ξ := by
  let hc := twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc
  let hs := twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs
  let d := constructedModularConjugationData L (twoStateMatrixVector Ω ξ) hs hc
    (tomitaPolarConjugation_commutant_eq L (twoStateMatrixVector Ω ξ) hs hc)
  let U := twoStatePositiveTransport M Ω ξ hc d
  have hU (a : Algebra M) (x : H) : U (a.val x)=a.val (U x) :=
    twoStatePositiveTransport_intertwines M Ω ξ hc d a x
  refine ⟨U.symm ξ,?_,U.symm.norm_map ξ,?_,?_,?_⟩
  · have hp : twoStateCornerEmbedding 0 (U.symm ξ) ∈
        canonicalModularPositiveCone L (twoStateMatrixVector Ω ξ) hs hc := by
      change twoStateCornerEmbedding 0 (U.symm ξ) ∈
        modularPositiveCone (M := twoStateMatrixAlgebra M) d.conjugation (twoStateMatrixVector Ω ξ)
      rw [twoStatePositiveTransport_inverse_reference M Ω ξ hc d]
      exact modularQuadratic_mem_positiveCone _ _ _
    exact (twoStateCorner_positive_iff M Ω ξ hΩc hξc hΩs hξs J L 0 (U.symm ξ)).mp hp
  · exact spatialVectorTransport_separating (StarAlgEquiv.refl ℂ (Algebra M)) U hU ξ hξs
  · exact spatialVectorTransport_cyclic (StarAlgEquiv.refl ℂ (Algebra M)) U hU ξ hξc
  · ext a
    exact spatialVectorTransport_state (StarAlgEquiv.refl ℂ (Algebra M)) U hU ξ a


/-- Only faithful vector states on the type III representation used below are
needed; a support isometry first makes the second vector cyclic. -/
theorem TypeIIIFactor.exists_positive_unit_state_representative
    [Nontrivial H] (hM : TypeIIIFactor M)
    (Ω : H) (hΩc : DenseRange (algebraVectorMap M Ω))
    (hΩs : Function.Injective (algebraVectorMap M Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (hξ : ‖ξ‖=1)
    (hξs : Function.Injective (algebraVectorMap M ξ)) :
    ∃ η : H, η ∈ canonicalModularPositiveCone J Ω hΩs hΩc ∧
      ‖η‖=1 ∧ Function.Injective (algebraVectorMap M η) ∧
      DenseRange (algebraVectorMap M η) ∧
      vectorFunctional (M := M) η=vectorFunctional ξ := by
  obtain ⟨ζ,hζ,hζc,hζs,he⟩ := hM.exists_cyclic_vector_same_state ξ hξ hξs
  obtain ⟨L,_⟩ := exists_hilbert_conjugation (H := TwoStateMatrixHilbert H H)
  obtain ⟨η,hη,hn,hs,hc,hstate⟩ :=
    exists_positive_representative_of_cyclic Ω ζ hΩc hζc hΩs hζs J L
  exact ⟨η,hη,hn.trans hζ,hs,hc,hstate.trans he⟩

end
end KadisonKastler

end OAI

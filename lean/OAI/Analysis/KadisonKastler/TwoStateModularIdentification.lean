import OAI.Analysis.KadisonKastler.TwoStateGraphCompression
import OAI.Analysis.KadisonKastler.TwoStateCornerCovariance
import OAI.Analysis.KadisonKastler.ModularIsometryTransport
import OAI.Analysis.KadisonKastler.ModularActionVector

namespace OAI

/-! # Identifying both diagonal modular actions with their original states -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
  (hΩs : Function.Injective (algebraVectorMap M Ω))
  (hξs : Function.Injective (algebraVectorMap M ξ))

omit [TopologicalSpace.SeparableSpace H] in
include hΩc hξc in
theorem twoStateVectorAt_cyclic (i : Fin 2) :
    DenseRange (algebraVectorMap M (twoStateVectorAt Ω ξ i)) := by
  fin_cases i
  · exact hΩc
  · exact hξc

omit [TopologicalSpace.SeparableSpace H] in
include hΩs hξs in
theorem twoStateVectorAt_separating (i : Fin 2) :
    Function.Injective (algebraVectorMap M (twoStateVectorAt Ω ξ i)) := by
  fin_cases i
  · exact hΩs
  · exact hξs

def twoStateConstructedResolution
    (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H) :
    ModularSpectralResolution (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ) :=
  constructedModularSpectralResolution L (twoStateMatrixVector Ω ξ)
    (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
    (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc)
    (modularStrongGroup_normalizes L (twoStateMatrixVector Ω ξ)
      (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
      (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc))

def twoStateCornerResolution (J : H ≃ₗᵢ⋆[ℂ] H) (i : Fin 2) :
    ModularSpectralResolution M (twoStateVectorAt Ω ξ i) :=
  constructedModularSpectralResolution J (twoStateVectorAt Ω ξ i)
    (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
    (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i)
    (modularStrongGroup_normalizes J (twoStateVectorAt Ω ξ i)
      (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
      (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i))

theorem twoStateCornerAction_identification (J : H ≃ₗᵢ⋆[ℂ] H)
    (L : TwoStateMatrixHilbert H H ≃ₗᵢ⋆[ℂ] TwoStateMatrixHilbert H H)
    (i : Fin 2) (t : Multiplicative ℝ) (a : Algebra M) :
    twoStateCornerAction M Ω ξ (twoStateConstructedResolution M Ω ξ hΩc hξc hΩs hξs L) i t a =
      modularAlgebraAut (twoStateCornerResolution M Ω ξ hΩc hξc hΩs hξs J i) t a := by
  apply twoStateVectorAt_separating M Ω ξ hΩs hξs i
  change (twoStateCornerAction M Ω ξ _ i t a).val (twoStateVectorAt Ω ξ i) =
    (modularAlgebraAut _ t a).val (twoStateVectorAt Ω ξ i)
  rw [modularAlgebraAut_vector]
  apply (twoStateCornerEmbedding i).injective
  rw [twoStateCornerAction_vector]
  exact modularStrongGroup_isometry J L (twoStateVectorAt Ω ξ i) (twoStateMatrixVector Ω ξ)
    (twoStateCornerEmbedding i) (twoStateCorner_resolvent M Ω ξ i J L 1)
    (twoStateVectorAt_separating M Ω ξ hΩs hξs i)
    (twoStateVectorAt_cyclic M Ω ξ hΩc hξc i)
    (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)
    (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc) t (a.val (twoStateVectorAt Ω ξ i))

end

end KadisonKastler

end OAI

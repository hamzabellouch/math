import OAI.Analysis.KadisonKastler.TwoStateMatrixState
import OAI.Analysis.KadisonKastler.ModularAlgebraAutomorphism
import OAI.Analysis.KadisonKastler.ModularSpectralConstruction
import OAI.Analysis.KadisonKastler.MatrixFixedCorners

namespace OAI

/-! # Modular automorphisms of the two-state matrix algebra -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)

def twoStateMatrixAut (m : ModularSpectralResolution (twoStateMatrixAlgebra M)
    (twoStateMatrixVector Ω ξ)) (t : Multiplicative ℝ) :
    CStarMatrix (Fin 2) (Fin 2) (Algebra M) ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) (Algebra M) :=
  ((twoStateMatrixEquiv M).trans (modularAlgebraAut m t)).trans (twoStateMatrixEquiv M).symm

theorem twoStateMatrixAut_fixes_diagonal (m : ModularSpectralResolution (twoStateMatrixAlgebra M)
    (twoStateMatrixVector Ω ξ)) (t : Multiplicative ℝ) (i : Fin 2) :
    twoStateMatrixAut M Ω ξ m t (matrixSlot i i 1) = matrixSlot i i 1 := by
  apply (twoStateMatrixEquiv M).injective
  change (twoStateMatrixEquiv M)
    ((twoStateMatrixEquiv M).symm
      (modularAlgebraAut m t (twoStateMatrixEquiv M (matrixSlot i i 1)))) = _
  rw [StarAlgEquiv.apply_symm_apply]
  exact modularAlgebraAut_fixed m t (twoStateMatrixProjection M i)
    (twoStateMatrixProjection_centralizes M Ω ξ i)

theorem twoStateMatrixAut_offDiagonal_unitary (m : ModularSpectralResolution (twoStateMatrixAlgebra M)
    (twoStateMatrixVector Ω ξ)) (t : Multiplicative ℝ) :
    matrixOffDiagonalCoefficient (twoStateMatrixAut M Ω ξ m t) ∈ unitary (Algebra M) :=
  matrixOffDiagonalCoefficient_unitary _
    (twoStateMatrixAut_fixes_diagonal M Ω ξ m t 0)
    (twoStateMatrixAut_fixes_diagonal M Ω ξ m t 1)

variable [TopologicalSpace.SeparableSpace H]

def twoStateModularResolution
    (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
    (hΩs : Function.Injective (algebraVectorMap M Ω))
    (hξs : Function.Injective (algebraVectorMap M ξ)) :
    ModularSpectralResolution (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ) :=
  (publishedModularSpectralResolution (TwoStateMatrixHilbert H H) (twoStateMatrixAlgebra M)
    (twoStateMatrixVector Ω ξ) (twoStateMatrixAlgebra_cyclic M Ω ξ hΩc hξc)
    (twoStateMatrixAlgebra_separating M Ω ξ hΩs hξs)).some.2

end

end KadisonKastler

end OAI

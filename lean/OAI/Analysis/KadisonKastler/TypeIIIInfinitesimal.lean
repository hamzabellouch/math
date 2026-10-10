import OAI.Analysis.KadisonKastler.TypeIIIMatrixCorner
import OAI.Analysis.KadisonKastler.CommutatorRangeError

namespace OAI

/-! # Uniform infinitesimal estimate for all separably acting type III factors

The matrix corner is constructed from a proper isometry and the published
comparison theorem. The tolerance therefore precedes the Hilbert space and
factor without any matrix-corner hypothesis in the conclusion.
-/

namespace KadisonKastler

noncomputable section

universe u

local instance typeIIIInfinitesimalSourceOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance typeIIIInfinitesimalSourceStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem uniform_typeIII_selfAdjoint_estimate
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    ∃ K : ℝ, 0 < K ∧ ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H], ∀ M : VonNeumannAlgebra H,
      TypeIIIFactor M → ∀ h : selfAdjoint (H →L[ℂ] H),
        Metric.infDist (h : H →L[ℂ] H) (selfAdjointAlgebraCommutantSum M) ≤
          K * commutatorRangeError M (h : H →L[ℂ] H) := by
  obtain ⟨K, hK, hbound⟩ := uniform_typeIII_selfAdjoint_infinitesimal_estimate
    hSpectral hCompare hSakai (fun P => hDistance P.H P.M)
  refine ⟨K, hK, ?_⟩
  intro H _ _ _ _ M hM h
  obtain ⟨p, _, F, hF⟩ := hM.exists_fullMatrixCorner hCompare
  let P : MatrixTypeIIIFactorModel := {
    H := H
    M := M
    isTypeIII := hM
    E := typeIIIInitialSpace p
    matrixCorner := F
    matrix_mem := hF }
  exact hbound P h h.property

end

end KadisonKastler

end OAI

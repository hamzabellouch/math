import OAI.Analysis.KadisonKastler.CommonPositionSpatial
import OAI.Analysis.KadisonKastler.ConjugateFactor
import OAI.Analysis.KadisonKastler.PublishedIncreasingMatrixInjectivity

namespace OAI

/-! # Removing the common-subfactor restriction

First move a constructed injective subfactor into the neighbor, then apply
common-position stability, and compose the two actual ambient unitaries.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {M N R : VonNeumannAlgebra H}

local instance finiteStabilityOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _

local instance finiteStabilityStarOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

local instance finiteStabilityOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _

local instance finiteStabilityOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The total displacement, including the initial injective embedding. -/
def finiteFactorError (t : ℝ) : ℝ := 150 * t + 2400 * commonPositionError (302 * t)

/-- An irreducible injective subfactor need not already belong to the neighbor. -/
theorem finiteFactor_spatial_of_injective_subfactor
    (hEmbedding : PublishedAmenableEmbedding (H := H))
    (hPosition : PublishedCommonTracialPosition.{u})
    (hBoundary : PublishedBoundary.{u})
    (hTom : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [TopologicalSpace.SeparableSpace K], PublishedFieldTomiyamaFamily K)
    (hpub : PublishedTracialUltrapower.{u})
    (hmat : PublishedFiniteMatrixUltraproduct)
    (hind : PublishedPopaFiniteBaseIndependence.{u})
    (hFock : PublishedDiagonalFockRepresentation.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hCyclic : ∀ (P : VonNeumannAlgebra H) (hP : Generator.IsII1Factor P.toStarSubalgebra)
      (θ : Algebra M ≃⋆ₐ[ℂ] Algebra P),
      PublishedCyclicSimilarity.{u, u} (A := Algebra (pairedVonNeumann hM hP θ)))
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (hRM : R ≤ M) (hR : IsInjective R)
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    {t : ℝ} (ht : 0 < t) (htEmbed : t < 1 / 100)
    (htPosition : 302 * t < 174 / 1000000000000000)
    (hgap : kkDistance M N < t)
    (htStandard : 3 * 50948 * Real.sqrt (302 * t) < 1 / 100000)
    (htSpatial : commonPositionError (302 * t) < 1 / 2400) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ finiteFactorError t := by
  obtain ⟨w, hRN, hw, hnear⟩ :=
    exists_common_amenable_neighbor_of_kkDistance_lt hEmbedding hRM hR hgap htEmbed
  let P := unitaryConjugateAlgebra (star w) N
  have hP : Generator.IsII1Factor P.toStarSubalgebra :=
    unitaryConjugateAlgebra_isII1 (star w) hN
  have hgapP : kkDistance M P < 302 * t := by
    change kkDistance M (unitaryConjugateAlgebra (star w) N) < _
    linarith
  obtain ⟨v, hv, hnorm⟩ := common_subfactor_spatial_stability
    hPosition hBoundary hTom hpub hmat hind hFock hM hP
    (hCyclic P hP) hCommutant hRM hRN hR hirr (by positivity)
    htPosition hgapP htStandard htSpatial
  refine ⟨w * v, conjugates_of_conjugated_neighbor w v hv, ?_⟩
  exact (conjugated_neighbor_displacement_le w v).trans (add_le_add hw hnorm)

/-- The matrix construction supplies the required subfactor in a tracial
representation; its injectivity is the stated published AFD implication. -/
theorem finiteFactor_spatial_in_tracial_representation
    (hMatrix : PublishedIncreasingMatrixInjectivity (H := H))
    (hEmbedding : PublishedAmenableEmbedding (H := H))
    (hPosition : PublishedCommonTracialPosition.{u})
    (hBoundary : PublishedBoundary.{u})
    (hTom : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [TopologicalSpace.SeparableSpace K], PublishedFieldTomiyamaFamily K)
    (hpub : PublishedTracialUltrapower.{u})
    (hmat : PublishedFiniteMatrixUltraproduct)
    (hind : PublishedPopaFiniteBaseIndependence.{u})
    (hFock : PublishedDiagonalFockRepresentation.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (τ : UltrapowerBridge.TracialRepresentation M)
    (hCyclic : ∀ (P : VonNeumannAlgebra H) (hP : Generator.IsII1Factor P.toStarSubalgebra)
      (θ : Algebra M ≃⋆ₐ[ℂ] Algebra P),
      PublishedCyclicSimilarity.{u, u} (A := Algebra (pairedVonNeumann hM hP θ)))
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    {t : ℝ} (ht : 0 < t) (htEmbed : t < 1 / 100)
    (htPosition : 302 * t < 174 / 1000000000000000)
    (hgap : kkDistance M N < t)
    (htStandard : 3 * 50948 * Real.sqrt (302 * t) < 1 / 100000)
    (htSpatial : commonPositionError (302 * t) < 1 / 2400) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ finiteFactorError t := by
  obtain ⟨R, hRM, _, hR, hirr⟩ := exists_irreducible_injective_subfactor hMatrix τ hM
  exact finiteFactor_spatial_of_injective_subfactor hEmbedding hPosition hBoundary hTom
    hpub hmat hind hFock hM hN hCyclic hCommutant hRM hR hirr ht htEmbed
    htPosition hgap htStandard htSpatial

end

end KadisonKastler

end OAI

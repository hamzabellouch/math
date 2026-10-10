import OAI.Analysis.KadisonKastler.ConstructedFiniteFactorStability
import OAI.Analysis.KadisonKastler.OriginalMatrixInjectivity
import OAI.Analysis.KadisonKastler.FiniteStageEmbedding

namespace OAI

/-! # Finite-factor stability with constructed matrix embeddings

Increasing matrix stages give the initial common position for the
nearby finite factors.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M N : VonNeumannAlgebra H}

local instance matrixFactorOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _

local instance matrixFactorStarOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

local instance matrixFactorOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _

local instance matrixFactorOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Common tracial position, boundary means and field projections give
a small unitary conjugacy for the finite factors. -/
theorem constructed_finiteFactor_spatial_of_matrixStages
    (hPosition : PublishedCommonTracialPosition.{u})
    (hBoundary : PublishedBoundary.{u})
    (hTom : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [TopologicalSpace.SeparableSpace K], PublishedFieldTomiyamaFamily K)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (A : ℕ → Generator.FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra (Generator.FiniteMatrixStage.generatedVonNeumann A),
        coordinateInclusion (Generator.FiniteMatrixStage.generatedVonNeumann_le A) r * a =
          a * coordinateInclusion (Generator.FiniteMatrixStage.generatedVonNeumann_le A) r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    {t : ℝ} (ht : 0 < t)
    (htPosition : 302 * t < 174 / 1000000000000000)
    (hgap : kkDistance M N < t)
    (htStandard : 3 * 50948 * Real.sqrt (302 * t) < 1 / 100000)
    (htSpatial : commonPositionError (302 * t) < 1 / 4000000) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ constructedFiniteFactorError t := by
  have : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with h | h
    · exact False.elim (hM.nonzero (@Subsingleton.elim (H →L[ℂ] H) inferInstance 0 1))
    · exact h
  have hRM := Generator.FiniteMatrixStage.generatedVonNeumann_le A
  have hR := isInjective_original_matrix_closure hM A hA
  obtain ⟨w, hRN, hw, hnear⟩ := exists_common_matrixStage_neighbor_of_kkDistance_lt
    A hA ht.le (by linarith : t ≤ 1 / 1152) hgap
  let P := unitaryConjugateAlgebra (star w) N
  have hP : Generator.IsII1Factor P.toStarSubalgebra :=
    unitaryConjugateAlgebra_isII1 (star w) hN
  have hgapP : kkDistance M P < 302 * t := by
    change kkDistance M (unitaryConjugateAlgebra (star w) N) < _
    linarith
  obtain ⟨v, hv, hnorm⟩ := constructed_common_subfactor_spatial_stability
    hPosition hBoundary hTom hM hP hRM hRN hR hirr (by positivity)
    htPosition hgapP htStandard htSpatial
  refine ⟨w * v, conjugates_of_conjugated_neighbor w v hv, ?_⟩
  exact (conjugated_neighbor_displacement_le w v).trans (add_le_add hw hnorm)

end

end KadisonKastler

end OAI

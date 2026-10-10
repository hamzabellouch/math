import OAI.Analysis.KadisonKastler.RegularCoreFiniteProjection
import OAI.Analysis.KadisonKastler.SemifiniteFactor

namespace OAI

/-! # Descent from a type II∞ regular core

All matrix, injectivity, and finite-corner data are constructed from the
ordinary projection-theoretic type II∞ predicate and the published countable
copy theorem. The source-core orientation is retained.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

local instance regularCoreSemifiniteOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance regularCoreSemifiniteStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- A type II∞ source core yields conjugacy on the original Hilbert space. -/
theorem regularCore_spatial_of_typeIIInfinity
    (h : FiniteFactorPublishedInputs.{u})
    (hComm : PublishedRegularCommutant.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (M N : VonNeumannAlgebra H)
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    (hM : ∀ s T, T ∈ M → unitaryConj (U s) T ∈ M)
    (hN : ∀ s T, T ∈ N → unitaryConj (U s) T ∈ N)
    (hCopies : PublishedProperInfiniteProjectionCopies.{u})
    (hCore : TypeIIInfinityFactor (regularCoreAlgebra U hU M))
    {t g : ℝ} (ht : 0 < t) (htEmbed : 302 * t < 1 / 100)
    (htPosition : 302 * (302 * t) < 174 / 1000000000000000)
    (hgapTensor : kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) < t)
    (hgap : kkDistance M N < g)
    (htStandard : 3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000)
    (htSpatial : commonPositionError (302 * (302 * t)) < 1 / 4000000)
    (htCP : 2 * matrixCornerError t < 1 / 1000)
    (hge : g + 2 * matrixCornerError t < 1) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧
      ‖(v : H →L[ℂ] H) - 1‖ ≤ 256 * matrixCornerError t := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let D : FiniteFullMatrixCornerData (regularCoreAlgebra U hU M) :=
    Classical.choice (hCore.nonempty_finiteMatrixCornerData hCopies)
  exact regularCore_spatial_of_matrix_corner h hComm hSpectral hDiagonal
    M N hCorrection hCommutant U hU hM hN (typeIIIInitialSpace D.projection)
    D.matrix D.matrix_mem D.corner_isII1
    ht htEmbed htPosition hgapTensor hgap htStandard htSpatial htCP hge

end

end KadisonKastler

end OAI

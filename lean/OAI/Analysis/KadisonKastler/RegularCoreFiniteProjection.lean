import OAI.Analysis.KadisonKastler.RegularCoreStability
import OAI.Analysis.KadisonKastler.PublishedProperInfiniteProjection

namespace OAI

/-! # Regular-core stability from one finite full projection

The published countable-copy theorem supplies the matrix geometry. The
represented corner's factor, finite and diffuse properties are proved by
compression, and the periodic matrix stages supply the injective subalgebra.
No corner type or stability conclusion is included in the projection input.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

local instance regularCoreFiniteProjectionOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance regularCoreFiniteProjectionStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- Only one nonzero finite projection in the properly infinite source core
is needed; the remaining matrix and II₁ corner data are constructed. -/
theorem regularCore_spatial_of_finite_full_projection
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
    (hInfinite : ProperlyInfiniteIdentity (regularCoreAlgebra U hU M))
    (hCoreFactor : ScalarCenter (regularCoreAlgebra U hU M))
    (p : Generator.Tracial.AlgebraProjection (regularCoreAlgebra U hU M))
    (hp : p.val ≠ 0) (hFinite : FiniteProjectionIn (regularCoreAlgebra U hU M) p.val)
    (hDiffuse : ∀ p : Algebra (regularCoreAlgebra U hU M),
      IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra (regularCoreAlgebra U hU M), IsStarProjection q ∧ q ≠ 0 ∧
        q ≠ p ∧ p * q = q ∧ q * p = q)
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
  obtain ⟨q, hq, hqFinite, F, hF⟩ := exists_finite_fullMatrixCorner_of_factor
    hCopies hInfinite hCoreFactor p hp hFinite
  have hE0 : (typeIIIInitialSpace q).starProjection ≠
      (0 : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    intro hz
    apply hq
    apply Subtype.ext
    exact (typeIIIInitialSpace_projection q).trans hz
  have hFinite' : FiniteProjectionIn (regularCoreAlgebra U hU M)
      ⟨(typeIIIInitialSpace q).starProjection, F.zero_zero ▸ hF 0 0⟩ := by
    have he : (⟨(typeIIIInitialSpace q).starProjection,
        F.zero_zero ▸ hF 0 0⟩ : Algebra (regularCoreAlgebra U hU M)) = q.val :=
      Subtype.ext (typeIIIInitialSpace_projection q).symm
    rw [he]
    exact hqFinite
  exact regularCore_spatial_of_finite_projection_matrix_corner
    h hComm hSpectral hDiagonal M N hCorrection hCommutant U hU hM hN
    (typeIIIInitialSpace q) F hF hCoreFactor hE0 hFinite' hDiffuse
    ht htEmbed htPosition hgapTensor hgap htStandard htSpatial htCP hge

end

end KadisonKastler

end OAI

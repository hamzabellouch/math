import OAI.Analysis.KadisonKastler.RegularCoreDescent
import OAI.Analysis.KadisonKastler.AmenableMatrixStability
import OAI.Analysis.KadisonKastler.FullMatrixInjectivity
import OAI.Analysis.KadisonKastler.CornerFactorStructure

namespace OAI

/-! # The finite-corner argument for the actual regular cores

This specializes the proved injective-matrix argument and character descent
to the concrete regular representation.  The semifinite matrix subalgebra
and its finite initial corner are explicit data.  In particular, none of
the action, fixed-point, or range-identification conclusions is assumed.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

local instance regularCoreStabilityFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance regularCoreStabilityFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- A tensor gap, an injective matrix subalgebra in the source regular
core, and an II₁ initial corner give the original-space conjugacy. -/
theorem regularCore_spatial_of_injective_matrix_subalgebra
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
    (S : VonNeumannAlgebra (RegularCoreHilbert H))
    (hSM : S ≤ regularCoreAlgebra U hU M) (hS : IsInjective S)
    (E : Submodule ℂ (RegularCoreHilbert H)) [CompleteSpace E]
    (F : FullMatrixCorner E) (hFS : ∀ i j, F.entry i j ∈ S)
    (hCorner : Generator.IsII1Factor
      (representedCorner E (regularCoreAlgebra U hU M)
        (F.zero_zero ▸ hSM (hFS 0 0))).toStarSubalgebra)
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
  have hgapCore : kkDistance (regularCoreAlgebra U hU M)
      (regularCoreAlgebra U hU N) < t :=
    (kkDistance_regularCore_le_tensor hComm U hU M N hM hN).trans_lt hgapTensor
  obtain ⟨z, hz, hn⟩ := F.spatial_of_injective_matrix_subalgebra h
    (regularCoreAlgebra U hU M) (regularCoreAlgebra U hU N)
    S hSM hS hFS hCorner ht htEmbed htPosition hgapCore htStandard htSpatial
  obtain ⟨v, hv, hvn⟩ := concrete_unitary_of_regularCore_conjugacy
    hComm hSpectral hDiagonal M N hCorrection hCommutant U hU hM hN z hz
    hgap (by linarith) (by linarith)
  exact ⟨v, hv, hvn.trans (mul_le_mul_of_nonneg_left hn (by norm_num))⟩

/-- The injective matrix subalgebra is constructed from the actual full
matrix corner by increasing factorial-period stages.  Thus the only
semifinite data left here are the full corner and its II₁ initial corner. -/
theorem regularCore_spatial_of_matrix_corner
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
    (E : Submodule ℂ (RegularCoreHilbert H)) [CompleteSpace E]
    (F : FullMatrixCorner E) (hF : ∀ i j, F.entry i j ∈ regularCoreAlgebra U hU M)
    (hCorner : Generator.IsII1Factor
      (representedCorner E (regularCoreAlgebra U hU M)
        (F.zero_zero ▸ hF 0 0)).toStarSubalgebra)
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
  obtain ⟨S, hSM, hS, hFS⟩ := F.exists_injective_algebra_containing_entries
    (regularCoreAlgebra U hU M) hF
  exact regularCore_spatial_of_injective_matrix_subalgebra h hComm hSpectral hDiagonal
    M N hCorrection hCommutant U hU hM hN S hSM hS E F hFS hCorner
    ht htEmbed htPosition hgapTensor hgap htStandard htSpatial htCP hge

/-- A finite nonzero first projection in the diffuse source factor suffices:
its actual II₁ corner is proved by compression, rather than assumed. The
countable matrix units and finite projection remain explicit geometric data. -/
theorem regularCore_spatial_of_finite_projection_matrix_corner
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
    (E : Submodule ℂ (RegularCoreHilbert H)) [CompleteSpace E]
    (F : FullMatrixCorner E) (hF : ∀ i j, F.entry i j ∈ regularCoreAlgebra U hU M)
    (hCoreFactor : ScalarCenter (regularCoreAlgebra U hU M))
    (hE0 : E.starProjection ≠ (0 : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hFinite : FiniteProjectionIn (regularCoreAlgebra U hU M)
      ⟨E.starProjection, F.zero_zero ▸ hF 0 0⟩)
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
  have hCorner := F.representedCorner_isII1 (regularCoreAlgebra U hU M) hF
    hCoreFactor hE0 hFinite hDiffuse
  exact regularCore_spatial_of_matrix_corner h hComm hSpectral hDiagonal
    M N hCorrection hCommutant U hU hM hN E F hF hCorner
    ht htEmbed htPosition hgapTensor hgap htStandard htSpatial htCP hge

end

end KadisonKastler

end OAI

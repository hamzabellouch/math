import OAI.Analysis.KadisonKastler.CharacterAverageDescent
import OAI.Analysis.KadisonKastler.AmenableMatrixStability

namespace OAI

/-! # The finite-corner argument followed by character descent

This combines the proved common-action gap estimate, injective-matrix
finite-corner conjugacy, and the actual character average. The concrete
core fixed-point identities remain explicit representation data.
-/

namespace KadisonKastler

noncomputable section

universe u v w s

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  {G : Type w} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  {L : Type s} [Group L] [TopologicalSpace L] [DiscreteTopology L]

local instance coreDescentFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance coreDescentFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- A small gap of the upper invariant algebras gives a concrete
conjugacy of the originals, with the finite-corner modulus. -/
theorem spatial_of_core_matrix_data
    (h : FiniteFactorPublishedInputs.{v}) (M N : VonNeumannAlgebra H)
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (mU : ScalarInvariantMean G) (mV : ScalarInvariantMean L)
    (U : G →* unitary (K →L[ℂ] K)) (V : L →* unitary (K →L[ℂ] K))
    (A B : VonNeumannAlgebra K)
    (hA : ∀ g T, T ∈ A → unitaryConj (U g) T ∈ A)
    (hB : ∀ g T, T ∈ B → unitaryConj (U g) T ∈ B)
    (hV : ∀ l T, T ∈ fixedPointAlgebra U B →
      unitaryConj (V l) T ∈ fixedPointAlgebra U B)
    (j : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (hj : Function.Injective j)
    (hjoint : (fixedPointAlgebra V (fixedPointAlgebra U B) : Set (K →L[ℂ] K)) =
      j '' (N : Set (H →L[ℂ] H)))
    (hjM : ∀ x : Algebra M, j x ∈ fixedPointAlgebra U A)
    (hjfix : ∀ l x, unitaryConj (V l) (j x) = j x)
    (S : VonNeumannAlgebra K) (hSCore : S ≤ fixedPointAlgebra U A)
    (hS : IsInjective S) (E : Submodule ℂ K) [CompleteSpace E]
    (F : FullMatrixCorner E) (hFS : ∀ i k, F.entry i k ∈ S)
    (hCorner : Generator.IsII1Factor
      (representedCorner E (fixedPointAlgebra U A)
        (F.zero_zero ▸ hSCore (hFS 0 0))).toStarSubalgebra)
    {t g : ℝ} (ht : 0 < t) (htEmbed : 302 * t < 1 / 100)
    (htPosition : 302 * (302 * t) < 174 / 1000000000000000)
    (hgapUp : kkDistance A B < t) (hgap : kkDistance M N < g)
    (htStandard : 3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000)
    (htSpatial : commonPositionError (302 * (302 * t)) < 1 / 4000000)
    (htCP : 2 * matrixCornerError t < 1 / 1000)
    (hge : g + 2 * matrixCornerError t < 1) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 256 * matrixCornerError t := by
  have hgapCore : kkDistance (fixedPointAlgebra U A) (fixedPointAlgebra U B) < t :=
    (mU.kkDistance_fixedPointAlgebra_le U A B hA hB).trans_lt hgapUp
  obtain ⟨z, hz, hn⟩ := F.spatial_of_injective_matrix_subalgebra h
    (fixedPointAlgebra U A) (fixedPointAlgebra U B) S hSCore hS hFS hCorner
    ht htEmbed htPosition hgapCore htStandard htSpatial
  obtain ⟨u, hu, hnorm⟩ := concrete_unitary_of_character_average hCorrection hCommutant
    mV U V A B j hj hV hjoint hjM hjfix z hz hgap (by linarith) (by linarith)
  exact ⟨u, hu, hnorm.trans (mul_le_mul_of_nonneg_left hn (by norm_num))⟩

end

end KadisonKastler

end OAI

import OAI.Analysis.KadisonKastler.AbelianInvariantMean
import OAI.Analysis.KadisonKastler.ModularActionCorrection
import OAI.Analysis.KadisonKastler.CoreMatrixDescent

namespace OAI

/-! # Abelian action correction and descent

Finite-Cesaro means give the scalar averaging used in the action and
fixed-point arguments. These results apply to the additive real modular
group and its character group, viewed as discrete abelian groups.
-/

namespace KadisonKastler

noncomputable section

universe u v w s

section CommonAction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type w} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- Correct nearby normalizers for an abelian action using an invariant
scalar mean and a normalizer factorization. -/
theorem exists_common_abelian_action_of_near_normalizers
    (hpub : PublishedNormalizerFactorization (H := H)) (P : VonNeumannAlgebra H)
    (U : G →* unitary (H →L[ℂ] H)) (v : G → unitary (H →L[ℂ] H))
    (hv : ∀ g, Conjugates (v g) P P)
    {d : ℝ} (hd : 0 ≤ d) (hsmall : 3 * d ≤ 1 / 4096)
    (hclose : ∀ g, ‖(v g : H →L[ℂ] H) - (U g : H →L[ℂ] H)‖ ≤ d) :
    ∃ q : unitary (H →L[ℂ] H), ‖(q : H →L[ℂ] H) - 1‖ ≤ 770 * d ∧
      ∀ g, Conjugates (U g) (unitaryConjugateAlgebra q P)
        (unitaryConjugateAlgebra q P) :=
  exists_common_action_of_near_normalizers hpub (abelianScalarInvariantMean G)
    P U v hv hd hsmall hclose

/-- Passage to fixed points of an abelian action decreases the gap. -/
theorem kkDistance_abelian_fixedPointAlgebra_le
    (U : G →* unitary (H →L[ℂ] H)) (M N : VonNeumannAlgebra H)
    (hM : ∀ g T, T ∈ M → unitaryConj (U g) T ∈ M)
    (hN : ∀ g T, T ∈ N → unitaryConj (U g) T ∈ N) :
    kkDistance (fixedPointAlgebra U M) (fixedPointAlgebra U N) ≤ kkDistance M N :=
  (abelianScalarInvariantMean G).kkDistance_fixedPointAlgebra_le U M N hM hN

end CommonAction

section CharacterDescent

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {G : Type w} [Group G] {L : Type s} [CommGroup L]
  [TopologicalSpace L] [DiscreteTopology L]
  {M N : VonNeumannAlgebra H}

local instance abelianDescentFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance abelianDescentFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- An abelian character action supplies its own averaging map in descent. -/
theorem concrete_unitary_of_abelian_character_average
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (U : G →* unitary (K →L[ℂ] K)) (V : L →* unitary (K →L[ℂ] K))
    (A B : VonNeumannAlgebra K)
    (j : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (hj : Function.Injective j)
    (hV : ∀ l T, T ∈ fixedPointAlgebra U B →
      unitaryConj (V l) T ∈ fixedPointAlgebra U B)
    (hjoint : (fixedPointAlgebra V (fixedPointAlgebra U B) : Set (K →L[ℂ] K)) =
      j '' (N : Set (H →L[ℂ] H)))
    (hjM : ∀ x : Algebra M, j x ∈ fixedPointAlgebra U A)
    (hjfix : ∀ l x, unitaryConj (V l) (j x) = j x)
    (z : unitary (K →L[ℂ] K))
    (hz : Conjugates z (fixedPointAlgebra U A) (fixedPointAlgebra U B))
    {g : ℝ} (hgap : kkDistance M N < g)
    (hsmall : 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1 / 1000)
    (hge : g + 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 256 * ‖(z : K →L[ℂ] K) - 1‖ :=
  concrete_unitary_of_character_average hCorrection hCommutant
    (abelianScalarInvariantMean L) U V A B j hj hV hjoint hjM hjfix z hz hgap hsmall hge

end CharacterDescent

section CoreDescent

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  {G : Type w} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  {L : Type s} [CommGroup L] [TopologicalSpace L] [DiscreteTopology L]

local instance abelianCoreFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance abelianCoreFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- The complete finite-corner/character descent for abelian actions, with
both averaging means constructed and all core representation data explicit. -/
theorem spatial_of_abelian_core_matrix_data
    (h : FiniteFactorPublishedInputs.{v}) (M N : VonNeumannAlgebra H)
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
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
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 256 * matrixCornerError t :=
  spatial_of_core_matrix_data h M N hCorrection hCommutant
    (abelianScalarInvariantMean G) (abelianScalarInvariantMean L)
    U V A B hA hB hV j hj hjoint hjM hjfix S hSCore hS E F hFS hCorner
    ht htEmbed htPosition hgapUp hgap htStandard htSpatial htCP hge

end CoreDescent

end

end KadisonKastler

end OAI

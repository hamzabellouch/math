import OAI.Analysis.KadisonKastler.RegularTensorGap

namespace OAI

/-! # Descent from the actual regular cores

The action, character multipliers, faithful embedding, and joint fixed
algebra are the concrete regular objects. The only structural inputs are
the published commutant and diagonal-decomposition
theorems. A supplied nearby core conjugacy descends by the proved scalar
character mean and UCP perturbation argument.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- A common full matrix corner supplies the complete tensor comparison
needed before taking the common-action fixed points. -/
theorem kkDistance_regularCore_le_of_common_matrix_units
    (hComm : PublishedRegularCommutant.{u})
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    (M N : VonNeumannAlgebra H)
    (hM : ∀ s T, T ∈ M → unitaryConj (U s) T ∈ M)
    (hN : ∀ s T, T ∈ N → unitaryConj (U s) T ∈ N)
    (D : Submodule ℂ H) [CompleteSpace D] (F : FullMatrixCorner D)
    (hFM : ∀ i j, F.entry i j ∈ M) (hFN : ∀ i j, F.entry i j ∈ N) :
    kkDistance (regularCoreAlgebra U hU M) (regularCoreAlgebra U hU N) ≤
      kkDistance M N :=
  (kkDistance_regularCore_le_tensor hComm U hU M N hM hN).trans
    (kkDistance_regularTensorAlgebra_le_of_common_matrix_units M N D F hFM hFN)

local instance regularCoreDescentFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance regularCoreDescentFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- The actual regular-core conjugacy descends to the original Hilbert
space with the quantitative UCP bound. -/
theorem concrete_unitary_of_regularCore_conjugacy
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
    (z : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hz : Conjugates z (regularCoreAlgebra U hU M) (regularCoreAlgebra U hU N))
    {g : ℝ} (hgap : kkDistance M N < g)
    (hsmall : 2 * ‖(z : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) - 1‖ < 1 / 1000)
    (hge : g + 2 * ‖(z : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) - 1‖ < 1) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧
      ‖(v : H →L[ℂ] H) - 1‖ ≤
        256 * ‖(z : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) - 1‖ := by
  have hz' : Conjugates z
      (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra M))
      (fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra N)) := by
    rwa [← regularCoreAlgebra_eq_fixed_of_published hComm U hU M hM,
      ← regularCoreAlgebra_eq_fixed_of_published hComm U hU N hN]
  have hjM (x : Algebra M) : regularCoreEmbedding U hU x ∈
      fixedPointAlgebra (regularCoreAction U) (regularTensorAlgebra M) := by
    rw [mem_fixedPointAlgebra_iff]
    exact ⟨regularCoreEmbedding_mem_tensorAlgebra U hU M hM x.property,
      fun s => regularCoreEmbedding_fixed U hU s x⟩
  let : TopologicalSpace (Multiplicative ℝ) := ⊥
  let : DiscreteTopology (Multiplicative ℝ) := ⟨rfl⟩
  exact concrete_unitary_of_abelian_character_average hCorrection hCommutant
    (regularCoreAction U) (regularCharacterRepresentation (H := H))
    (regularTensorAlgebra M) (regularTensorAlgebra N)
    (regularCoreEmbedding U hU) (regularCoreEmbedding_injective U hU)
    (fun a T hT => regularCharacter_normalizes_coreFixed U N a hT)
    (regular_jointFixed_coe U hU hSpectral hDiagonal N hN) hjM
    (fun a x => regularCharacter_fixes_embedding U hU a.toAdd x)
    z hz' hgap hsmall hge

end

end KadisonKastler

end OAI

import OAI.Analysis.KadisonKastler.MatrixPairPreparation
import OAI.Analysis.KadisonKastler.ConjugateFactor

namespace OAI

/-! # Two-correction preparation for actual increasing matrix stages

The faithful trace vector discharges the injectivity premise using the
tracial matrix-closure theorem while preserving the state, expectation,
vector, and modular-conjugation data.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixStagePairOrder (Q : VonNeumannAlgebra H) :
    PartialOrder (Algebra Q) := CStarAlgebra.spectralOrder _
local instance matrixStagePairStarOrder (Q : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra Q) := CStarAlgebra.spectralOrderedRing _

/-- Returning through the two actual preparation corrections adds their
displacements, while preserving the strict final tolerance. -/
theorem nearConjugacy_of_matrixPair_preparation
    (M N : VonNeumannAlgebra H) (a b : unitary (H →L[ℂ] H)) {γ ε : ℝ}
    (ha : ‖(a : H →L[ℂ] H) - 1‖ ≤ 150 * γ)
    (hb : ‖(b : H →L[ℂ] H) - 1‖ ≤ 45300 * γ)
    (h : NearConjugacy M
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)) ε) :
    NearConjugacy M N (45450 * γ + ε) := by
  obtain ⟨v, hv, hnorm⟩ := h
  refine ⟨a * (b * v), ?_, ?_⟩
  · exact conjugates_of_conjugated_neighbor a (b * v)
      (conjugates_of_conjugated_neighbor b v hv)
  · calc
      ‖((a * (b * v) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ ≤
          ‖(a : H →L[ℂ] H) - 1‖ + ‖((b * v : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ :=
        norm_unitary_mul_sub_one_le a (b * v)
      _ ≤ ‖(a : H →L[ℂ] H) - 1‖ +
          (‖(b : H →L[ℂ] H) - 1‖ + ‖(v : H →L[ℂ] H) - 1‖) :=
        add_le_add le_rfl (norm_unitary_mul_sub_one_le b v)
      _ ≤ 150 * γ + (45300 * γ + ‖(v : H →L[ℂ] H) - 1‖) :=
        add_le_add ha (add_le_add hb le_rfl)
      _ < 150 * γ + (45300 * γ + ε) := by linarith
      _ = 45450 * γ + ε := by ring

/-- Increasing full matrix stages give both amenable corrections and the
cyclic separating vector of the final neighbor. No separate injectivity
assumption on the generated algebra is needed. -/
theorem exists_matrixStagePair_preparation
    (hDistance : ∀ Q : VonNeumannAlgebra H,
      PublishedBlockCommutantApproximation (Algebra Q) H)
    (M N : VonNeumannAlgebra H) (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : FaithfulTracialState (Algebra (FiniteMatrixStage.generatedVonNeumann A)))
    (P : Algebra M →L[ℂ] Algebra (FiniteMatrixStage.generatedVonNeumann A))
    (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann A)) (x : Algebra M),
      P (StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le A) r * x) =
        r * P x)
    (hright : ∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann A)) (x : Algebra M),
      P (x * StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le A) r) =
        P x * r)
    (Ω : H) (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (d : ModularConjugationData M Ω)
    (hirr : ∀ T ∈ M,
      (∀ r ∈ FiniteMatrixStage.generatedVonNeumann A, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 200000)
    (hgap : kkDistance M N < γ)
    (hMN : MatrixNearInclusion M N γ) (hNM : MatrixNearInclusion N M γ) :
    ∃ a b : unitary (H →L[ℂ] H),
      ‖(a : H →L[ℂ] H) - 1‖ ≤ 150 * γ ∧
      ‖(b : H →L[ℂ] H) - 1‖ ≤ 45300 * γ ∧
      let N₂ := unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)
      FiniteMatrixStage.generatedVonNeumann A ≤ N₂ ∧
      conjugateRightAlgebra d.conjugation d.involutive
        (FiniteMatrixStage.generatedVonNeumann A) ≤ N₂.commutant ∧
      MatrixNearInclusion M N₂ (90901 * γ) ∧
      MatrixNearInclusion N₂ M (90901 * γ) ∧
      kkDistance M N₂ < 90902 * γ ∧
      DenseRange (algebraVectorMap N₂ Ω) ∧
      Function.Injective (algebraVectorMap N₂ Ω) ∧
      DenseRange (algebraVectorMap N₂.commutant Ω) ∧
      Function.Injective (algebraVectorMap N₂.commutant Ω) := by
  exact exists_matrixPair_preparation hDistance M N
    (FiniteMatrixStage.generatedVonNeumann A) (FiniteMatrixStage.generatedVonNeumann_le A)
    τ P hP hleft hright Ω hΩ d
    (fun n => (A n).size) (matrixStageConcreteUnits A)
    (by simpa only [matrixStageConcreteUnits_algebra] using hA)
    (generated_matrixStages_eq A hA) hirr hγ hsmall hgap hMN hNM

end

end KadisonKastler

end OAI

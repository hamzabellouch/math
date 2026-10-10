import Mathlib
import OAI.Analysis.WeakInfiniteness.MatrixCutToolkit
import OAI.Analysis.WeakInfiniteness.CuntzCopies
import OAI.Analysis.WeakInfiniteness.CutImplementation

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance matrixRealModuleColumns {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

lemma uniformCopies_absorbs {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (a : A) (ha : 0 ≤ a) (d : ℕ) :
    CuntzSubequiv (diagonalCopies d a) (diagonalCopies n a) := by
  by_cases haz : a=0
  · subst a
    intro ε hε
    refine ⟨0, ?_⟩
    simpa [diagonalCopies] using hε
  · exact (hpi a ha haz).diagonal_absorbs hn d

lemma exists_finite_model_columns {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (c : A) {α : ℝ} (hα : 0 < α) (d : ℕ) :
    ∃ L : CStarMatrix (Fin n) (Fin d) A,
      L.conjTranspose*L=diagonalCopies d (cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) c)) ∧
      L*L.conjTranspose ∈ hereditarySubalgebra (diagonalCopies n (positiveCut (α/2) c))
        (diagonalCopies_nonneg n (positiveCut_nonneg (α/2) c)).isSelfAdjoint ∧
      ‖L‖ ≤ 1 ∧ diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)*L=L := by
  let c₁ := positiveCut (α/2) c
  have hc₁ : 0 ≤ c₁ := positiveCut_nonneg _ _
  obtain ⟨L,hL,hLher,hLn⟩ := (uniformCopies_absorbs hn hpi c₁ hc₁ d).exact_spectralRamp
    (diagonalCopies_nonneg d hc₁) (diagonalCopies_nonneg n hc₁) (α/8) (by positivity)
  refine ⟨L, ?_, hLher, hLn, ?_⟩
  · rw [hL, diagonalCopies_cfc d c₁ hc₁.isSelfAdjoint (spectralRamp (α/8))
      (continuous_spectralRamp _) (spectralRamp_eq_zero (by positivity) (by positivity))]
  · apply rectangular_left_identity_of_hereditary_range _ _ L
      (diagonalCopies_nonneg n hc₁).isSelfAdjoint _ hLher
    change (diagonalHom n (cfcₙ (spectralRamp (α/4)) c))*(diagonalHom n c₁)=diagonalHom n c₁
    rw [← map_mul]
    congr 1
    exact spectralRamp_mul_positiveCut c (by positivity) (by linarith)

end

end WeakPureInfiniteness
end

end OAI

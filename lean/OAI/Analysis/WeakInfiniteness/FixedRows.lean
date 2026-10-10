import Mathlib
import OAI.Analysis.WeakInfiniteness.CutImplementation
import OAI.Analysis.WeakInfiniteness.MatrixCutToolkit

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

local instance matrixRealModuleRows {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

lemma exists_fixed_comparison_row {n : ℕ} (c h : A) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hch : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h))
    {α : ℝ} (hα : 0 < α) :
    ∃ R : CStarMatrix (Fin 1) (Fin n) A,
      R.conjTranspose*R=diagonalCopies n (cfcₙ (spectralRamp (α/4)) c) ∧
      R*R.conjTranspose∈hereditarySubalgebra (diagonalCopies 1 h)
        (diagonalCopies_nonneg 1 hh).isSelfAdjoint ∧ ‖R‖≤1 := by
  obtain ⟨R,hR,hRh,hRn⟩ := hch.exact_spectralRamp
    (diagonalCopies_nonneg n hc) (diagonalCopies_nonneg 1 hh) (α/4) (by positivity)
  refine ⟨R,?_,hRh,hRn⟩
  rw [hR, diagonalCopies_cfc n c hc.isSelfAdjoint (spectralRamp (α/4))
    (continuous_spectralRamp _) (spectralRamp_eq_zero (by positivity) (by positivity))]

omit [PartialOrder A] [StarOrderedRing A] in
lemma spectralRamp_mul_ramp (c : A) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 2*θ ≤ δ) :
    cfcₙ (spectralRamp θ) c*cfcₙ (spectralRamp δ) c=cfcₙ (spectralRamp δ) c := by
  have hd : 0 < δ := lt_of_lt_of_le (by linarith : 0 < 2*θ) hδ
  by_cases hc : IsSelfAdjoint c
  · rw [← cfcₙ_mul (spectralRamp θ) (spectralRamp δ) c
      (continuous_spectralRamp _).continuousOn (spectralRamp_eq_zero hθ (by positivity))
      (continuous_spectralRamp _).continuousOn (spectralRamp_eq_zero hd (by positivity))]
    apply cfcₙ_congr
    intro s hs
    dsimp only
    by_cases hsd : s ≤ δ
    · rw [spectralRamp_eq_zero hd hsd, mul_zero]
    · rw [spectralRamp_eq_one hθ (hδ.trans (le_of_lt (lt_of_not_ge hsd))), one_mul]
  · simp only [cfcₙ_apply_of_not_predicate c hc, mul_zero]

lemma fixed_row_shallow_support {n : ℕ} (c : A)
    {α : ℝ} (hα : 0 < α) (R : CStarMatrix (Fin 1) (Fin n) A)
    (hR : R.conjTranspose*R=diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)) :
    diagonalCopies n (cfcₙ (spectralRamp (α/16)) c)*R.conjTranspose=R.conjTranspose := by
  apply rectangular_left_identity_of_range
  rw [rectangular_conjTranspose_conjTranspose, hR]
  change diagonalHom n (cfcₙ (spectralRamp (α/16)) c)*
    diagonalHom n (cfcₙ (spectralRamp (α/4)) c)=diagonalHom n (cfcₙ (spectralRamp (α/4)) c)
  rw [← map_mul, spectralRamp_mul_ramp c (by positivity : 0 < α/16) (by linarith)]

lemma fixed_row_partial_isometry {n : ℕ} (p h : A) (hh : 0 ≤ h)
    (hph : star p*p*h=h) (R : CStarMatrix (Fin 1) (Fin n) A)
    (hR : R*R.conjTranspose∈hereditarySubalgebra (diagonalCopies 1 h)
      (diagonalCopies_nonneg 1 hh).isSelfAdjoint) :
    diagonalCopies 1 (star p*p)*R=R := by
  apply rectangular_left_identity_of_hereditary_range _ _ R
    (diagonalCopies_nonneg 1 hh).isSelfAdjoint _ hR
  change diagonalHom 1 (star p*p)*diagonalHom 1 h=diagonalHom 1 h
  rw [← map_mul, hph]

end

end WeakPureInfiniteness
end

end OAI

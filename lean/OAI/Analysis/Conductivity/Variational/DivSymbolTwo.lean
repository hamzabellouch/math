import Mathlib
import OAI.Analysis.Conductivity.Flux.FluxPotentialSymbol

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Matrix

def divSymbolTwo (ξ : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 5) ℝ :=
  !![ξ 0, ξ 1, 0, ξ 2, 0; 0, ξ 0, ξ 1, 0, ξ 2]

def divAdjointTwo (ξ : Fin 3 → ℝ) : Matrix (Fin 5) (Fin 2) ℝ :=
  !![ξ 0, 0; ξ 1 / 2, ξ 0 / 2; 0, ξ 1; ξ 2, 0; 0, ξ 2]

theorem divSymbolTwo_gram_det (ξ : Fin 3 → ℝ) :
    (divSymbolTwo ξ * divAdjointTwo ξ).det =
      (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) *
        ((ξ 0 ^ 2 + ξ 1 ^ 2) / 2 + ξ 2 ^ 2) := by
  simp [divSymbolTwo, divAdjointTwo, Matrix.det_fin_two]
  ring

theorem divSymbolTwo_gram_det_pos {ξ : Fin 3 → ℝ} (hξ : ξ ≠ 0) :
    0 < (divSymbolTwo ξ * divAdjointTwo ξ).det := by
  have hp : 0 < ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 := by
    by_contra hn
    have h0 : ξ 0 = 0 := by nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 2)]
    have h1 : ξ 1 = 0 := by nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 2)]
    have h2 : ξ 2 = 0 := by nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1)]
    apply hξ
    funext i
    fin_cases i <;> assumption
  rw [divSymbolTwo_gram_det]
  exact mul_pos hp (by nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1), sq_nonneg (ξ 2)])

theorem divSymbolTwo_surjective {ξ : Fin 3 → ℝ} (hξ : ξ ≠ 0) :
    Function.Surjective (divSymbolTwo ξ).mulVec := by
  intro v
  refine ⟨divAdjointTwo ξ *ᵥ ((divSymbolTwo ξ * divAdjointTwo ξ)⁻¹ *ᵥ v), ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt (divSymbolTwo_gram_det_pos hξ))),
    Matrix.one_mulVec]

theorem twoField_potential_range {ξ : Fin 3 → ℝ} (hξ : ξ ≠ 0) :
    Set.range (fluxPotentialSymbol (divSymbolTwo ξ) (divAdjointTwo ξ)).mulVec =
      {v | divSymbolTwo ξ *ᵥ v = 0} :=
  fluxPotentialSymbol_range _ _ (ne_of_gt (divSymbolTwo_gram_det_pos hξ))

end ScalarConductivity

end

end OAI

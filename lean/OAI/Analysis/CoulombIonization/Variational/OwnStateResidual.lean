import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.OwnProbabilityTailTiltBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.ShellResidualControl

namespace OAI

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
noncomputable section
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

lemma OwnProbabilityTailTiltState.mono_error {Z lam r δ δ' : ℝ} {N K : ℕ}
    {p₀ : Fin (K+1) → ℝ} {F : fermionGraph N}
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ δ F) (hδ : δ ≤ δ') :
    OwnProbabilityTailTiltState Z lam r K p₀ δ' F := by
  refine ⟨hF.1,hF.2.1.trans (add_le_add le_rfl hδ),?_⟩
  intro j A hA hp
  obtain ⟨G,hGn,hGlaw,hGE⟩ := hF.2.2 j A hA hp
  exact ⟨G,hGn,hGlaw,hGE.trans (by unfold dyadicUniformEventBudget; exact add_le_add le_rfl hδ)⟩

lemma normalized_sector_excess_le {Z η : ℝ} {N : ℕ} (F : fermionGraph N)
    (hFn : ‖fermionGraphValue N F‖^2 = 1)
    (hFE : formEnergy Z (graphFormVector F) ≤ energy Z N+η) :
    (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η := by
  have he := sectorExcessOperator_diagonal Z F
  have hev : energy Z N * ‖fermionGraphValue N F‖^2 = energy Z N :=
    (congrArg (fun t : ℝ => energy Z N*t) hFn).trans (mul_one _)
  exact he.le.trans ((sub_le_sub_left hev.ge _).trans
    (sub_le_iff_le_add.mpr (by linarith only [hFE])))

lemma exists_small_error_product {A : ℝ} (hA : 0 ≤ A) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η*A ≤ 1 := by
  let η := min 1 (A+1)⁻¹
  have hη : 0 < η := lt_min zero_lt_one (inv_pos.2 (by linarith))
  refine ⟨η,hη,min_le_left _ _,?_⟩
  have hh := mul_le_mul_of_nonneg_right (min_le_right 1 (A+1)⁻¹) (by linarith : 0 ≤ A+1)
  have he : (A+1)⁻¹*(A+1) = 1 := inv_mul_cancel₀ (by linarith)
  change η*(A+1) ≤ _ at hh
  rw [he] at hh
  nlinarith only [hh,hη.le]

lemma own_state_graph_bound {Z lam r η : ℝ} {N K : ℕ}
    {p₀ : Fin (K+1) → ℝ} (hZ : 0 ≤ Z) (hη : η ≤ 1) (F : fermionGraph N)
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ η F) :
    ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) := by
  exact near_minimizer_graph_bound hZ F hF.1
    (hF.2.1.trans (add_le_add le_rfl hη))

def SmallSectorResidual {N : ℕ} (Z η : ℝ) (F : fermionGraph N) : Prop :=
  (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η ∧
  ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2)

lemma smallSectorResidual_of_own {Z lam r η : ℝ} {N K : ℕ}
    {p₀ : Fin (K+1) → ℝ} (hZ : 0 ≤ Z) (hη : η ≤ 1) (F : fermionGraph N)
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ η F) : SmallSectorResidual Z η F :=
  ⟨normalized_sector_excess_le F hF.1 hF.2.1, own_state_graph_bound hZ hη F hF⟩

lemma exists_own_state_small_residual {Z lam r η : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hr : 0 < r) (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : PriceMinimizes (energy Z) lam N) (K : ℕ) (p₀ : Fin (K+1) → ℝ)
    (h₀ : ∀ j, 0 < p₀ j) :
    ∃ F : fermionGraph N, OwnProbabilityTailTiltState Z lam r K p₀ 1 F ∧
      SmallSectorResidual Z η F := by
  obtain ⟨F,hF⟩ := exists_actual_own_probability_tail_tilt_state hZ hr hN K p₀ h₀ hη
  exact ⟨F,hF.mono_error hη1,smallSectorResidual_of_own hZ hη1 F hF⟩

lemma exists_own_state_shell_residual {Z lam r v : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hr : 0 < r) (_hv : 0 < v)
    (hN : PriceMinimizes (energy Z) lam N) (K : ℕ) (p₀ : Fin (K+1) → ℝ)
    (h₀ : ∀ j, 0 < p₀ j) :
    ∃ (F : fermionGraph N) (η : ℝ),
      OwnProbabilityTailTiltState Z lam r K p₀ 1 F ∧ 0 ≤ η ∧ SmallSectorResidual Z η F ∧
      η*(‖sectorExcessOperator Z N‖*shellGraphConstant N v*
        (4*(|energy Z N|+(N:ℝ)*Z^2+2))) ≤ 1^2 := by
  let B := 4*(|energy Z N|+(N:ℝ)*Z^2+2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let A := ‖sectorExcessOperator Z N‖*shellGraphConstant N v*B
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (norm_nonneg _) (shellGraphConstant_nonneg N v)) hB
  obtain ⟨η,hη,hη1,hηA⟩ := exists_small_error_product hA
  obtain ⟨F,hF,hres⟩ := exists_own_state_small_residual hZ hr hη hη1 hN K p₀ h₀
  refine ⟨F,η,hF,hη.le,hres,?_⟩
  exact hηA.trans_eq (by norm_num)
end CoulombAtom

end

end OAI

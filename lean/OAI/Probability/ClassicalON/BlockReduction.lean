import OAI.Probability.ClassicalON.BlockKernel

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem coordinateSpinMean_block_bounds (k : ℕ) (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) (x y : V) (C : ℝ)
    (hthree : ∀ c : E → ℝ,(∀ e,0 ≤ c e ∧ c e ≤ b e) →
      0 ≤ freeSpinMean 3 left right c (firstSpinProduct x y) ∧
        freeSpinMean 3 left right c (firstSpinProduct x y) ≤ C) :
    0 ≤ freeSpinMean (3+k) left right b (coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y) ∧
      freeSpinMean (3+k) left right b (coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y) ≤ C := by
  let : NeZero (3+k) := ⟨by omega⟩
  let W : (V → Spin (3+k)) → ℝ := fun s => Real.exp (freeSpinEnergy (3+k) left right b s)
  let F := coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y
  have hW : Continuous W := (continuous_freeSpinEnergy _ _ _ _).rexp
  have hF : Continuous F := continuous_coordinateSpinProduct _ _ _ _
  have hWF : Continuous (fun s => W s*F s) := hW.mul hF
  have hpoint (s : V → Spin (3+k)) :
      0 ≤ (∫ t,W (blockFiberConfiguration k s t)*F (blockFiberConfiguration k s t) ∂freeSpinReference 3) ∧
      (∫ t,W (blockFiberConfiguration k s t)*F (blockFiberConfiguration k s t) ∂freeSpinReference 3) ≤
        C*(∫ t,W (blockFiberConfiguration k s t) ∂freeSpinReference 3) := by
    dsimp only [W,F]
    rw [block_fiber_numerator,block_fiber_partition]
    have h3 := hthree (blockCoupling k left right b s) (blockCoupling_bounds k left right b hb s)
    have hr0 : 0 ≤ blockRadius k (s x)*blockRadius k (s y) :=
      mul_nonneg (blockRadius_nonneg _ _) (blockRadius_nonneg _ _)
    have hr1 : blockRadius k (s x)*blockRadius k (s y) ≤ 1 :=
      (mul_le_of_le_one_left (blockRadius_nonneg _ _) (blockRadius_le_one _ _)).trans
        (blockRadius_le_one _ _)
    have hD : 0 ≤ Real.exp (blockTailEnergy k left right b s)*
        freeSpinPartition 3 left right (blockCoupling k left right b s) :=
      mul_nonneg (Real.exp_pos _).le (freeSpinPartition_pos _ _ _ _).le
    constructor
    · exact mul_nonneg hD (mul_nonneg hr0 h3.1)
    · calc
        _ ≤ (Real.exp (blockTailEnergy k left right b s)*
            freeSpinPartition 3 left right (blockCoupling k left right b s))*C :=
          mul_le_mul_of_nonneg_left
            ((mul_le_of_le_one_left h3.1 hr1).trans h3.2) hD
        _ = _ := mul_comm _ _
  have hNi : Integrable (fun s : V → Spin (3+k) =>
      ∫ t,W (blockFiberConfiguration k s t)*F (blockFiberConfiguration k s t) ∂freeSpinReference 3)
        (freeSpinReference (3+k)) :=
    compact_integrable (compact_parametric_integral _
      (hWF.comp (continuous_blockFiberConfiguration k)))
  have hDi : Integrable (fun s : V → Spin (3+k) =>
      ∫ t,W (blockFiberConfiguration k s t) ∂freeSpinReference 3) (freeSpinReference (3+k)) :=
    compact_integrable (compact_parametric_integral _
      (hW.comp (continuous_blockFiberConfiguration k)))
  have hN : 0 ≤ ∫ s,W s*F s ∂freeSpinReference (3+k) := by
    rw [integral_freeSpinReference_block k _ hWF]
    exact integral_nonneg (fun s => (hpoint s).1)
  have hND : (∫ s,W s*F s ∂freeSpinReference (3+k)) ≤ C*(∫ s,W s ∂freeSpinReference (3+k)) := by
    rw [integral_freeSpinReference_block k _ hWF,integral_freeSpinReference_block k _ hW,← integral_const_mul]
    exact integral_mono hNi (hDi.const_mul C) (fun s => (hpoint s).2)
  have hD : 0 < ∫ s,W s ∂freeSpinReference (3+k) :=
    compact_integral_pos hW (fun _ => Real.exp_pos _)
  constructor
  · exact div_nonneg hN hD.le
  · exact (div_le_iff₀ hD).mpr hND

end ClassicalON

end

end OAI

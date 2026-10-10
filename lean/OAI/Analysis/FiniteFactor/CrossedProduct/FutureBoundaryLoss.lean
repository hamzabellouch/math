import OAI.Analysis.FiniteFactor.CrossedProduct.FutureBoundary
import OAI.Analysis.FiniteFactor.CrossedProduct.FutureBudget

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceFutureBoundary_loss_bound (j : ℕ) :
    (sourceBiasedLaw j) (sourceFutureBoundaryEvent j)ᶜ ≤
      ENNReal.ofReal (80*((sourceStageState j).K : ℝ)/(sourceStageState (j+1)).K) := by
  have hb (n : ℕ) : (sourceBiasedLaw j) (⋃ i : Fin (sourceBlockSize (j+1+n)), sourceFutureBad j n i) ≤
      ENNReal.ofReal (40*((sourceStageState j).K : ℝ)/(sourceStageState (j+1+n)).K) := by
    apply (measure_iUnion_le _).trans
    rw [tsum_fintype]
    apply (Finset.sum_le_sum (fun i _ => sourceFutureBad_bound j n i)).trans_eq
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by dsimp [sourceExclusionWidth]; positivity)]
    congr 1
    simp only [sourceExclusionWidth,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [(sourceBlockSize_pos (j+1+n)).ne',(sourceCutoff_pos (j+1+n)).ne']
    ring
  have hs : Summable (fun n : ℕ => 1/((sourceStageState (j+1+n)).K : ℝ)) :=
    sourceCutoff_reciprocal_summable.comp_injective (fun a b h => by omega)
  have he (n : ℕ) : 40*((sourceStageState j).K : ℝ)/(sourceStageState (j+1+n)).K =
      (40*((sourceStageState j).K : ℝ))*(1/((sourceStageState (j+1+n)).K : ℝ)) := by ring
  have hss : Summable (fun n : ℕ => 40*((sourceStageState j).K : ℝ)/(sourceStageState (j+1+n)).K) := by
    simp_rw [he]
    exact hs.mul_left _
  rw [sourceFutureBoundaryEvent,compl_compl]
  apply (measure_iUnion_le _).trans
  apply (ENNReal.tsum_le_tsum hb).trans
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hss]
  apply ENNReal.ofReal_le_ofReal
  simp_rw [he]
  rw [tsum_mul_left]
  calc
    _ ≤ (40*((sourceStageState j).K : ℝ))*(2/((sourceStageState (j+1)).K : ℝ)) :=
      mul_le_mul_of_nonneg_left (sourceCutoff_tail_bound (j+1)) (by positivity)
    _ = _ := by ring

theorem sourceFutureBoundary_loss_tendsto :
    Tendsto (fun j : ℕ => (sourceBiasedLaw j).real (sourceFutureBoundaryEvent j)ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => ENNReal.toReal_nonneg)
    (fun j => ENNReal.toReal_le_of_le_ofReal (by positivity) (sourceFutureBoundary_loss_bound j))
  exact sourceFutureBudget_tendsto

end
end FiniteFactor

end OAI

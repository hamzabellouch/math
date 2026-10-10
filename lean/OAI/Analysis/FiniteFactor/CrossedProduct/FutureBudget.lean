import OAI.Analysis.FiniteFactor.OrbitSampling.Tail
import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseDecay

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The exact recursive cutoff is at least m_j squared, giving vanishing
future boundary loss rather than merely geometric cutoff growth. -/
theorem sourceNextCutoff_ge_square (m : ℕ) (hm : 100 ≤ m) :
    (m : ℝ)^2 ≤ (sourceNextCutoff m : ℝ) := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (m : ℝ)^2 ≤ (m : ℝ)^((3/4 : ℝ)*(m : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  exact hp.trans (Nat.le_ceil _)

theorem sourceCutoff_ratio_tendsto :
    Tendsto (fun j : ℕ => ((sourceStageState j).K : ℝ)/(sourceStageState (j+1)).K) atTop (𝓝 0) := by
  have hbound (j : ℕ) : ((sourceStageState j).K : ℝ)/(sourceStageState (j+1)).K ≤
      1/(sourceBlockSize j : ℝ) := by
    have hm := sourceBlockSize_pos j
    have hK := sourceCutoff_pos (j+1)
    have hnext : (sourceBlockSize j : ℝ)^2 ≤ (sourceStageState (j+1)).K :=
      sourceNextCutoff_ge_square (sourceBlockSize j) (sourceStage j).m_ge_100
    have hprev : ((sourceStageState j).K : ℝ) ≤ sourceBlockSize j := by exact_mod_cast (sourceStage j).m_ge_K
    apply (div_le_div_iff₀ hK hm).mpr
    nlinarith
  have ht : Tendsto (fun j : ℕ => (sourceBlockSize j : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  apply squeeze_zero (fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hbound
  simpa only [one_div] using ht

theorem sourceFutureBudget_tendsto :
    Tendsto (fun j : ℕ => 80*((sourceStageState j).K : ℝ)/(sourceStageState (j+1)).K) atTop (𝓝 0) := by
  simpa only [mul_div_assoc,mul_zero] using sourceCutoff_ratio_tendsto.const_mul 80

end
end FiniteFactor

end OAI

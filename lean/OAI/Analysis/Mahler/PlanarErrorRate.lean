import OAI.Analysis.Mahler.FiberPrimitive

namespace OAI

namespace SymmetricMahler
open Real Filter
open scoped Topology

noncomputable def planarErrorConstant : ℝ :=
  Real.pi*(2/sqrt (4/Real.pi^2)+sqrt (2/(2/Real.pi^2))*(1+4/exp 1))

lemma planarErrorConstant_pos : 0 < planarErrorConstant := by
  unfold planarErrorConstant
  positivity

/-- The explicit uniform error has inverse-square-root-log
rate, with a constant independent of the point and the vertical section. -/
theorem planarError_rate {m : ℝ} (hm : 3 ≤ m) :
    planarError m ≤ planarErrorConstant/sqrt (log m) := by
  have hm0 : 0 < m := by linarith
  have hl0 : 0 < log m := log_pos (by linarith)
  have hlog : log m ≤ m := (log_le_sub_one_of_pos hm0).trans (by linarith)
  have hi : 1/sqrt m ≤ 1/sqrt (log m) := by
    exact one_div_le_one_div_of_le (sqrt_pos.mpr hl0) (sqrt_le_sqrt hlog)
  have hp := (cutoff_power_bound hm).trans hi
  have hs := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2/sqrt (4/Real.pi^2) by positivity)
  have houter : sqrt (2/((2/Real.pi^2)*log m)) = sqrt (2/(2/Real.pi^2))/sqrt (log m) := by
    rw [← sqrt_div (show 0 ≤ 2/(2/Real.pi^2) by positivity)]
    congr 1
    field_simp
  have henv : errorEnvelope m ≤
      (2/sqrt (4/Real.pi^2)+sqrt (2/(2/Real.pi^2))*(1+4/exp 1))/sqrt (log m) := by
    unfold errorEnvelope
    rw [houter]
    calc
      _ = (2/sqrt (4/Real.pi^2))*(m*(radialCutoff m)^(2*m-3/2 : ℝ)) +
          sqrt (2/(2/Real.pi^2))/sqrt (log m)*(1+4/exp 1) := by ring
      _ ≤ (2/sqrt (4/Real.pi^2))*(1/sqrt (log m)) +
          sqrt (2/(2/Real.pi^2))/sqrt (log m)*(1+4/exp 1) := add_le_add hs le_rfl
      _ = _ := by ring
  unfold planarError
  apply max_le
  · exact div_nonneg planarErrorConstant_pos.le (sqrt_nonneg _)
  · have h := mul_le_mul_of_nonneg_left henv Real.pi_pos.le
    simpa only [planarErrorConstant,mul_div_assoc] using h

lemma planarError_nat_tendsto_zero :
    Tendsto (fun m : ℕ => planarError (m : ℝ)) atTop (𝓝 0) :=
  planarError_tendsto_zero.comp tendsto_natCast_atTop_atTop

end SymmetricMahler

end OAI

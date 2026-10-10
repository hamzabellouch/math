import OAI.NumberTheory.JointDickman.Counting.HistogramWindowOverlap

namespace OAI

/-! # Uniform size bounds for endpoint logarithmic windows -/

namespace JointDickman
open Finset

theorem endpoint_histogram_window_length {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {a b N : ℝ} (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N) :
    ((histogramWindowCells (channelFineCount m B)
      (Real.log (a*N)/B) (Real.log (b*N)/B)).card : ℝ)*
        channelMesh (channelFineCount m B) ≤ (Real.log (b/a)+2)/B := by
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hb : 0 < b := ha.trans_le hab
  have horder := div_le_div_of_nonneg_right
    (Real.log_le_log (mul_pos ha hN) (mul_le_mul_of_nonneg_right hab hN.le)) hB0.le
  have hwin := histogramWindowCells_length (channelFineCount_pos hm hBpos) horder
  have heq : Real.log (b*N)/B-Real.log (a*N)/B = Real.log (b/a)/B := by
    rw [Real.log_mul hb.ne' hN.ne',Real.log_mul ha.ne' hN.ne',Real.log_div hb.ne' ha.ne']
    ring
  rw [heq] at hwin
  have hp : (B : ℝ)^(-(1/10 : ℝ)) ≤ 1 := by
    simpa using (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (-(1/10 : ℝ)) ≤ 0))
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound (B := B) hm hBpos).trans hp
  refine hwin.trans ?_
  apply (le_div_iff₀ hB0).mpr
  have hc : Real.log (b/a)/B*(B : ℝ) = Real.log (b/a) := div_mul_cancel₀ _ hB0.ne'
  nlinarith

/-- The enlarged cell window changes the upper physical scale by at most exp(1). -/
theorem endpoint_histogram_window_scale {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {a b N : ℝ} (hb : 0 < b) (hN : 0 < N)
    {i : Fin (channelFineCount m B)}
    (hi : i ∈ histogramWindowCells (channelFineCount m B)
      (Real.log (a*N)/B) (Real.log (b*N)/B))
    {x : ℝ} (hx : x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i)) :
    Real.exp ((B : ℝ)*x)/N ≤ b*Real.exp 1 := by
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hcell := (mem_filter.mp hi).2.1
  have hp : (B : ℝ)^(-(1/10 : ℝ)) ≤ 1 := by
    simpa using (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (-(1/10 : ℝ)) ≤ 0))
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound (B := B) hm hBpos).trans hp
  have hwidth := channel_width (channelFineCount m B) i
  have hup : (B : ℝ)*x ≤ Real.log (b*N)+1 := by
    have hl := (le_div_iff₀ hB0).mp hcell
    have hm := mul_le_mul_of_nonneg_left hx.2 hB0.le
    nlinarith
  apply (div_le_iff₀ hN).mpr
  calc
    Real.exp ((B : ℝ)*x) ≤ Real.exp (Real.log (b*N)+1) := Real.exp_le_exp.mpr hup
    _ = b*Real.exp 1*N := by rw [Real.exp_add,Real.exp_log (mul_pos hb hN)]; ring

end JointDickman

end OAI

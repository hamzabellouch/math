import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingEstimates

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem kernel_average_square_remainder_le {m : ℕ} (hm : 200 ≤ m) :
    ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 ≤
      4 * (m : ℝ)^(-(6 / 5 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hhalf := manuscript_width_le_half hm
  have hwidth : 0 < (m : ℝ)^(-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hm0 _
  have hden : (1 / 4 : ℝ) ≤ (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by nlinarith
  have hsquare : ((m : ℝ)^(-(3 / 5 : ℝ)))^2 = (m : ℝ)^(-(6 / 5 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hm0.le]
    congr 1
    norm_num
  calc
    _ ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 / 4) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
    _ = _ := by rw [hsquare]; ring

theorem twice_kernel_square_mass_le {m : ℕ} (hm : 200 ≤ m) :
    2 * ((2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2)) ≤
      8 * (m : ℝ)^(3 / 5 : ℝ) * Real.log (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog : Real.log ((m : ℝ)^2 / 2) ≤ 2 * Real.log (m : ℝ) := by
    calc
      _ ≤ Real.log ((m : ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (m : ℝ)])
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [Real.rpow_neg hm0.le, div_inv_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hlog (Real.rpow_pos_of_pos hm0 (3 / 5 : ℝ)).le]

theorem KernelEstimates.average_square_source_bound {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : KernelEstimates m u) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2) ≤
      1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) :=
  hu.average_square_upper.trans (add_le_add le_rfl (kernel_average_square_remainder_le hm))

theorem KernelEstimates.twice_square_mass_source_bound {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : KernelEstimates m u) :
    2 * (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u s v^2) ≤
      8 * (m : ℝ)^(3 / 5 : ℝ) * Real.log (m : ℝ) := by
  rw [hu.square_mass]
  exact twice_kernel_square_mass_le hm

end Invariant233.ScalarSampling

end

end OAI

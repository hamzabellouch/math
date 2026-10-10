import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingEstimates

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem KernelEstimates.average_square_rate {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : KernelEstimates m u) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2) ≤
      1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) := by
  have hh := manuscript_width_le_half hm
  have hnonneg : 0 ≤ (m : ℝ)^(-(3 / 5 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hden : (1 / 4 : ℝ) ≤ (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by nlinarith
  have hdenpos : 0 < (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := lt_of_lt_of_le (by norm_num) hden
  have hrate : ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
      (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 ≤
      4 * ((m : ℝ)^(-(3 / 5 : ℝ)))^2 := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith [mul_nonneg (sq_nonneg ((m : ℝ)^(-(3 / 5 : ℝ))))
      (sub_nonneg.mpr hden)]
  have hpow : ((m : ℝ)^(-(3 / 5 : ℝ)))^2 = (m : ℝ)^(-(6 / 5 : ℝ)) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg m)]
    congr 1
    norm_num
  calc
    _ ≤ 1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := hu.average_square_upper
    _ ≤ 1 + 4 * ((m : ℝ)^(-(3 / 5 : ℝ)))^2 := by linarith [hrate]
    _ = _ := by rw [hpow]

theorem KernelEstimates.twice_square_mass_rate {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : KernelEstimates m u) :
    2 * (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u s v^2) ≤
      8 * (m : ℝ)^(3 / 5 : ℝ) * Real.log m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog : Real.log ((m : ℝ)^2 / 2) ≤ 2 * Real.log m := by
    calc
      _ ≤ Real.log ((m : ℝ)^2) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (m : ℝ)])
      _ = _ := by rw [Real.log_pow]; norm_num
  calc
    _ = 4 * (m : ℝ)^(3 / 5 : ℝ) * Real.log ((m : ℝ)^2 / 2) := by
      rw [hu.square_mass, Real.rpow_neg hmpos.le]
      simp only [div_inv_eq_mul]
      ring
    _ ≤ (4 * (m : ℝ)^(3 / 5 : ℝ)) * (2 * Real.log m) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

theorem manuscript_average_square_rates {m : ℕ} (hm : 200 ≤ m) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) ≤
        1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) ∧
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v)^2) ≤
        1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) :=
  ⟨(all_kernel_estimates m hm).1.average_square_rate hm,
    (all_kernel_estimates m hm).2.average_square_rate hm⟩

theorem manuscript_twice_square_mass_rates {m : ℕ} (hm : 200 ≤ m) :
    2 * (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptKernel m s v^2) ≤
        8 * (m : ℝ)^(3 / 5 : ℝ) * Real.log m ∧
    2 * (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v^2) ≤
        8 * (m : ℝ)^(3 / 5 : ℝ) * Real.log m :=
  ⟨(all_kernel_estimates m hm).1.twice_square_mass_rate hm,
    (all_kernel_estimates m hm).2.twice_square_mass_rate hm⟩

end Invariant233.ScalarSampling

end

end OAI

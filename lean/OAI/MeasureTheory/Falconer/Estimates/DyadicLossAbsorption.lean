import OAI.MeasureTheory.Falconer.Slicing.GaussianLossAbsorption

namespace OAI

/-! # The logarithmic number of dyadic tests fits inside the chosen power loss -/

namespace Falconer
open Real Filter
open scoped Topology

theorem dyadic_log_depth (N : ℕ) :
    1-Real.log (1/(2:ℝ)^N)/Real.log 2 = (N:ℝ)+1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [one_div,Real.log_inv,Real.log_pow]
  field_simp
  ring

theorem eventually_dyadic_loss_absorption {ε κ : ℝ} (hεκ : ε < κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ C*(1-Real.log δ/Real.log 2)*δ^(-ε) ≤ δ^(-κ) := by
  have hr : 0 < κ-ε := sub_pos.mpr hεκ
  have hp : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝[>] 0) (𝓝 0) := by
    have hp₀ : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [Real.zero_rpow hr.ne'] using (Real.continuous_rpow_const hr.le).tendsto (0:ℝ)
    exact hp₀.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero hr
  have ht : Tendsto (fun δ : ℝ => C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_div,sub_zero,mul_zero] using (hp.sub (hl.div_const (Real.log 2))).const_mul C
  have hsmall := ht.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hsmall,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hs hδone
  have hδ := hδone.1
  refine ⟨hδ,?_⟩
  calc
    _ = (C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))*δ^(-κ) := by
      calc
        _ = C*(1-Real.log δ/Real.log 2)*δ^((κ-ε)+(-κ)) := by congr 2; ring
        _ = C*(1-Real.log δ/Real.log 2)*(δ^(κ-ε)*δ^(-κ)) := by rw [Real.rpow_add hδ]
        _ = _ := by ring
    _ ≤ 1*δ^(-κ) := mul_le_mul_of_nonneg_right hs.le (Real.rpow_nonneg hδ.le _)
    _ = _ := one_mul _

end Falconer

end OAI

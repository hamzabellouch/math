import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology Ring
namespace BrownLog
variable {A : Type*} [NormedRing A] [CompleteSpace A]
lemma summable_pow_of_root_tendsto (a : A)
    (ha : Tendsto (fun n:ℕ=>‖a^n‖^(1/(n:ℝ))) atTop (𝓝 0)) : Summable (fun n:ℕ=>a^n) := by
  have he : ∀ᶠ n : ℕ in atTop,0<n ∧ ‖a^n‖^(1/(n:ℝ))≤(1/2:ℝ) := by
    filter_upwards [eventually_gt_atTop 0,ha.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with n hn h
    exact ⟨hn,h.le⟩
  apply (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).of_norm_bounded_eventually_nat
  filter_upwards [he] with n hn
  have h := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hn.2 n
  have hi : (‖a^n‖^(1/(n:ℝ)))^n=‖a^n‖ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
    rw [one_div_mul_cancel (by exact_mod_cast hn.1.ne'),Real.rpow_one]
  rwa [hi] at h

omit [CompleteSpace A] in
lemma norm_root_smul_tendsto {𝕜 : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 A]
    (a : A) (c : 𝕜) (ha : Tendsto (fun n:ℕ=>‖a^n‖^(1/(n:ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n:ℕ=>‖(c•a)^n‖^(1/(n:ℝ))) atTop (𝓝 0) := by
  have hc := ha.const_mul ‖c‖
  simp only [mul_zero] at hc
  apply hc.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [smul_pow,norm_smul,norm_pow c n,Real.mul_rpow (by positivity) (norm_nonneg _)]
  rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg c)]
  rw [mul_one_div_cancel (by exact_mod_cast hn.ne'),Real.rpow_one]

omit [CompleteSpace A] in
lemma inverse_one_sub_eq_tsum (a : A) (ha : Summable (fun n:ℕ=>a^n)) :
    IsUnit (1-a) ∧ (1-a)⁻¹ʳ=∑' n:ℕ,a^n := by
  let u : Aˣ := ⟨1-a,∑' n:ℕ,a^n,ha.one_sub_mul_tsum_pow,ha.tsum_pow_mul_one_sub⟩
  refine ⟨u.isUnit,?_⟩
  change (↑u:A)⁻¹ʳ=(↑u⁻¹:A)
  exact Ring.inverse_unit u
end BrownLog
end

end OAI

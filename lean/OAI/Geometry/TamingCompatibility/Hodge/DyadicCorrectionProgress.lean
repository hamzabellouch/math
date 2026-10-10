import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped BigOperators

lemma sum_halves (N : ℕ) :
    ∑ j ∈ Finset.range N, (1/2:ℝ)^j = 2*(1-(1/2:ℝ)^N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,pow_succ]
    ring

lemma sum_halves_le_two (N : ℕ) :
    ∑ j ∈ Finset.range N, (1/2:ℝ)^j ≤ 2 := by
  rw [sum_halves]
  have : 0 ≤ (1/2:ℝ)^N := by positivity
  linarith

variable {V : Type*} [SeminormedAddCommGroup V]

lemma dyadic_norm_sum_inverse_bound (v : ℕ → V) (N : ℕ) {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C)
    (hv : ∀ j < N, ‖v j‖ ≤ (C/a)*(1/2:ℝ)^j) :
    ‖∑ j ∈ Finset.range N, v j‖ ≤ 2*C/a := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖v j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, (C/a)*(1/2:ℝ)^j :=
      Finset.sum_le_sum (fun j hj => hv j (Finset.mem_range.mp hj))
    _ = (C/a) * ∑ j ∈ Finset.range N, (1/2:ℝ)^j := (Finset.mul_sum _ _ _).symm
    _ ≤ (C/a)*2 := mul_le_mul_of_nonneg_left (sum_halves_le_two N) (div_nonneg hC ha.le)
    _ = _ := by ring

lemma dyadic_count_bound {a : ℝ} (ha : 0 < a) (N : ℕ)
    (hscale : a*(2:ℝ)^N ≤ 2) :
    (N:ℝ) ≤ 1 + |Real.log a| / Real.log 2 := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hpow : 0 < (2:ℝ)^N := by positivity
  have h := Real.log_le_log (mul_pos ha hpow) hscale
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hpow),Real.log_pow] at h
  have he : 1 + |Real.log a| / Real.log 2 =
      (Real.log 2 + |Real.log a|)/Real.log 2 := by field_simp
  rw [he]
  apply (le_div_iff₀ hlog).mpr
  nlinarith [neg_le_abs (Real.log a)]

lemma dyadic_norm_sum_log_bound (v : ℕ → V) (N : ℕ) {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hscale : a*(2:ℝ)^N ≤ 2)
    (hv : ∀ j < N, ‖v j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, v j‖ ≤ C*(1+|Real.log a|/Real.log 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range N, C :=
      Finset.sum_le_sum (fun j hj => hv j (Finset.mem_range.mp hj))
    _ = C*(N:ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_count_bound ha N hscale) hC

end TamingCompatibility.RadialPotential

end

end OAI

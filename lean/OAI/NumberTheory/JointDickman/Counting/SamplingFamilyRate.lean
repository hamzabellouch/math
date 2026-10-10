import OAI.NumberTheory.JointDickman.Counting.SamplingErrorBounds

namespace OAI

/-! # The column-family entropy is absorbed by concentration -/

namespace JointDickman
open Filter
open scoped Topology

theorem samplingFamily_scale_bound {B c K a : ℝ} {N m : ℕ}
    (hB : 1 ≤ B) (hc : 0 < c) (hK : 0 < K) (hN : 0 < N)
    (hNlo : c*B^(0.32 : ℝ) ≤ N) (hNhi : (2 : ℝ)*N ≤ B)
    (hm : (m : ℝ) ≤ 2*B^(0.14 : ℝ)) :
    (((2*N)^m : ℕ) : ℝ)*Real.exp (-(a^2*(N : ℝ))/(8*(K*B^(0.07 : ℝ))^2)) ≤
      Real.exp (2*(B^(0.14 : ℝ)*Real.log B) -
        (a^2*c/(8*K^2))*B^(0.18 : ℝ)) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hn : (0 : ℝ) < 2*N := by exact_mod_cast (Nat.mul_pos (by omega) hN)
  have hlog : (m : ℝ)*Real.log (2*N) ≤ 2*(B^(0.14 : ℝ)*Real.log B) := by
    have hh := mul_le_mul hm (Real.log_le_log hn hNhi)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*N by omega)))
      (by positivity : 0 ≤ 2*B^(0.14 : ℝ))
    convert hh using 1
    ring
  have hquot : (a^2*c/(8*K^2))*B^(0.18 : ℝ) ≤
      (a^2*(N : ℝ))/(8*(K*B^(0.07 : ℝ))^2) := by
    calc
      _ = (a^2*(c*B^(0.32 : ℝ)))/(8*(K*B^(0.07 : ℝ))^2) := by
        have he : (B^(0.07 : ℝ))^2*B^(0.18 : ℝ) = B^(0.32 : ℝ) := by
          rw [← Real.rpow_natCast,← Real.rpow_mul hB0.le,← Real.rpow_add hB0]
          norm_num
        field_simp
        nlinarith [he]
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNlo (sq_nonneg a)) (by positivity)
  have he : (((2*N)^m : ℕ) : ℝ) = Real.exp ((m : ℝ)*Real.log (2*N)) := by
    rw [Real.exp_nat_mul,Real.exp_log hn]
    push_cast
    rfl
  rw [he,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [sub_eq_add_neg,neg_div] using sub_le_sub hlog hquot

theorem samplingFamily_envelope_tendsto {c K a : ℝ}
    (hc : 0 < c) (hK : 0 < K) (ha : 0 < a) :
    Tendsto (fun B : ℝ => Real.exp (2*(B^(0.14 : ℝ)*Real.log B) -
      (a^2*c/(8*K^2))*B^(0.18 : ℝ))) atTop (𝓝 0) := by
  have hpos : 0 < a^2*c/(8*K^2) := by positivity
  convert sampling_union_bound_tendsto_zero hpos 2 using 1
  norm_num

theorem sampling_sites_le_scale (U : ℝ) :
    ∀ᶠ B : ℝ in atTop, ∀ N : ℕ, (N : ℝ) ≤ U*B^(0.32 : ℝ) → (2 : ℝ)*N ≤ B := by
  have ht : Tendsto (fun B : ℝ => (2*U)*(B^(0.32 : ℝ)/B^((1 : ℝ)))) atTop (𝓝 0) := by
    simpa using (power_div_power_tendsto_zero (a := (0.32 : ℝ)) (b := 1)
      (by norm_num)).const_mul (2*U)
  have hh := ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hh,eventually_gt_atTop (0 : ℝ)] with B hlim hB
  intro N hN
  rw [Real.rpow_one] at hlim
  have he : 2*U*B^(0.32 : ℝ) < B := by
    rw [← mul_div_assoc] at hlim
    have h := (div_lt_iff₀ hB).mp hlim
    simpa using h
  nlinarith

theorem sampling_sample_size {B : ℝ} (hB : 1 ≤ B) :
    0 < ⌈B^(0.14 : ℝ)⌉₊ ∧
      B^(0.14 : ℝ) ≤ (⌈B^(0.14 : ℝ)⌉₊ : ℝ) ∧
      (⌈B^(0.14 : ℝ)⌉₊ : ℝ) ≤ 2*B^(0.14 : ℝ) := by
  have hp : 0 < B^(0.14 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans_le hB) _
  have hone : 1 ≤ B^(0.14 : ℝ) := Real.one_le_rpow hB (by norm_num)
  exact ⟨Nat.ceil_pos.mpr hp,Nat.le_ceil _,by linarith [Nat.ceil_lt_add_one hp.le]⟩

end JointDickman

end OAI

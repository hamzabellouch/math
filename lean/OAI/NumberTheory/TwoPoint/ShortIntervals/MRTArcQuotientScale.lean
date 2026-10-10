import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcSubdivision
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionArcScale

namespace OAI

/-! The correction divisor and the gcd divisor together cost at most
W^6. These bounds retain the actual floor quotients after subdivision. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_arc_combined_divisor {W : ℝ} {d b : ℕ}
    (hW : 0 ≤ W) (hd : (d : ℝ) ≤ W ^ (5 : ℕ)) (hb : (b : ℝ) ≤ W) :
    ((d * b : ℕ) : ℝ) ≤ W ^ (6 : ℕ) := by
  push_cast
  calc
    (d : ℝ) * b ≤ W ^ (5 : ℕ) * W :=
      mul_le_mul hd hb (Nat.cast_nonneg b) (pow_nonneg hW _)
    _ = _ := by ring

lemma mrt_arc_quotient_window_lower {W H : ℝ} {h c : ℕ}
    (hW : 0 < W) (hc : 0 < c) (hcW : (c : ℝ) ≤ W ^ (6 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    H / W ^ (8 : ℕ) ≤ (h / c + 1 : ℕ) := by
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hquot : (h : ℝ) / c < (h / c + 1 : ℕ) := by
    apply (div_lt_iff₀ hcr).mpr
    have ht : (h : ℝ) < (c : ℝ) * (h / c + 1 : ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ h hc
    simpa only [mul_comm] using ht
  calc
    H / W ^ (8 : ℕ) = (H / W ^ (2 : ℕ)) / W ^ (6 : ℕ) := by
      rw [div_div, ← pow_add]
    _ ≤ (h : ℝ) / W ^ (6 : ℕ) := div_le_div_of_nonneg_right hh (pow_nonneg hW.le _)
    _ ≤ (h : ℝ) / c := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hcr hcW
    _ ≤ _ := hquot.le

lemma mrt_arc_quotient_window_power {W H : ℝ} {h c : ℕ}
    (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H)
    (hc : 0 < c) (hcW : (c : ℝ) ≤ W ^ (6 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    W ^ (242 : ℕ) ≤ (h / c + 1 : ℕ) := by
  have hW0 : 0 < W := by linarith
  calc
    W ^ (242 : ℕ) = W ^ (250 : ℕ) / W ^ (8 : ℕ) := by
      rw [show (250 : ℕ) = 242 + 8 by decide, pow_add]
      exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hW0.ne')).symm
    _ ≤ H / W ^ (8 : ℕ) := div_le_div_of_nonneg_right hH (pow_nonneg hW0.le _)
    _ ≤ _ := mrt_arc_quotient_window_lower hW0 hc hcW hh

lemma mrt_arc_quotient_window_log {W H : ℝ} {h c : ℕ}
    (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H)
    (hc : 0 < c) (hcW : (c : ℝ) ≤ W ^ (6 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    (121 / 125 : ℝ) * Real.log H ≤ Real.log (h / c + 1 : ℕ) := by
  have hW0 : 0 < W := by linarith
  have hH0 : 0 < H := (pow_pos hW0 250).trans_le hH
  have hpow := Real.log_le_log (pow_pos hW0 250) hH
  rw [Real.log_pow] at hpow
  norm_num only [Nat.cast_ofNat] at hpow
  have hlo := Real.log_le_log (div_pos hH0 (pow_pos hW0 8))
    (mrt_arc_quotient_window_lower hW0 hc hcW hh)
  rw [Real.log_div hH0.ne' (pow_ne_zero 8 hW0.ne'), Real.log_pow] at hlo
  norm_num only [Nat.cast_ofNat] at hlo
  linarith

lemma mrt_arc_quotient_prime_ratio {W H Q : ℝ} {h c : ℕ}
    (hW : 0 < W) (hH : 0 < H) (hQ : Q ≤ H / W ^ (3 : ℕ))
    (hc : 0 < c) (hcW : (c : ℝ) ≤ W ^ (6 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    Q / (h / c + 1 : ℕ) ≤ W ^ (5 : ℕ) := by
  have hlen := mrt_arc_quotient_window_lower hW hc hcW hh
  have hlen0 : (0 : ℝ) < (h / c + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hlen0).mpr
  calc
    Q ≤ H / W ^ (3 : ℕ) := hQ
    _ = W ^ (5 : ℕ) * (H / W ^ (8 : ℕ)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlen (pow_nonneg hW.le _)

/-- All corrected and gcd-divided outer cutoffs have comparable logarithms.
The exponent 1/170 leaves room for the combined W^6 denominator. -/
theorem mrt_arc_quotient_outer_logs :
    ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log (X : ℝ) ∧
      ∀ W : ℝ, 1 ≤ W → W ≤ (Real.log (X : ℝ)) ^ (1 / 170 : ℝ) →
      ∀ c : ℕ, 0 < c → (c : ℝ) ≤ W ^ (6 : ℕ) →
        Real.log (X : ℝ) / 2 ≤ Real.log (X / c + 1 : ℕ) ∧
        Real.log (X / c + 1 : ℕ) ≤ 2 * Real.log (X : ℝ) := by
  filter_upwards [mrt_correction_outer_log_scale] with X hX
  refine ⟨hX.1, ?_⟩
  intro W hW hWX c hc hcW
  have hW0 : 0 < W := by linarith
  have hL0 : 0 < Real.log (X : ℝ) := by linarith [hX.1]
  have hv1 : 1 ≤ W ^ (6 / 5 : ℝ) := Real.one_le_rpow hW (by norm_num)
  have hv : W ^ (6 / 5 : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) := by
    calc
      _ ≤ ((Real.log (X : ℝ)) ^ (1 / 170 : ℝ)) ^ (6 / 5 : ℝ) :=
        Real.rpow_le_rpow hW0.le hWX (by norm_num)
      _ = (Real.log (X : ℝ)) ^ (3 / 425 : ℝ) := by
        rw [← Real.rpow_mul hL0.le]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith [hX.1]) (by norm_num)
  have hp : (W ^ (6 / 5 : ℝ)) ^ (5 : ℕ) = W ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    norm_num
  exact hX.2 _ hv1 hv c hc (by rwa [hp])

/-- The longer prefix cutoff used after partial summation loses W^4
before the two divisor extractions. -/
lemma mrt_arc_long_prefix_quotient_lower {W H : ℝ} {h c : ℕ}
    (hW : 0 < W) (hc : 0 < c) (hcW : (c:ℝ) ≤ W^6)
    (hh : H/W^4 ≤ (h:ℝ)) :
    H/W^10 ≤ (h/c+1:ℕ) := by
  have hcr : (0:ℝ) < c := by exact_mod_cast hc
  have hquot : (h:ℝ)/c < (h/c+1:ℕ) := by
    apply (div_lt_iff₀ hcr).mpr
    have ht : (h:ℝ) < (c:ℝ)*(h/c+1:ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ h hc
    simpa only [mul_comm] using ht
  calc
    H/W^10 = (H/W^4)/W^6 := by rw [div_div,← pow_add]
    _ ≤ (h:ℝ)/W^6 := div_le_div_of_nonneg_right hh (pow_nonneg hW.le _)
    _ ≤ (h:ℝ)/c := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hcr hcW
    _ ≤ _ := hquot.le

lemma mrt_arc_long_prefix_quotient_power {W H : ℝ} {h c : ℕ}
    (hW : 1 ≤ W) (hH : W^250 ≤ H)
    (hc : 0 < c) (hcW : (c:ℝ) ≤ W^6)
    (hh : H/W^4 ≤ (h:ℝ)) :
    W^240 ≤ (h/c+1:ℕ) := by
  have hW0 : 0 < W := by linarith
  calc
    W^240 = W^250/W^10 := by
      rw [show (250:ℕ)=240+10 by decide,pow_add]
      exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hW0.ne')).symm
    _ ≤ H/W^10 := div_le_div_of_nonneg_right hH (pow_nonneg hW0.le _)
    _ ≤ _ := mrt_arc_long_prefix_quotient_lower hW0 hc hcW hh

lemma mrt_arc_long_prefix_quotient_log {W H : ℝ} {h c : ℕ}
    (hW : 1 ≤ W) (hH : W^250 ≤ H)
    (hc : 0 < c) (hcW : (c:ℝ) ≤ W^6)
    (hh : H/W^4 ≤ (h:ℝ)) :
    (24/25:ℝ)*Real.log H ≤ Real.log (h/c+1:ℕ) := by
  have hW0 : 0 < W := by linarith
  have hH0 : 0 < H := (pow_pos hW0 250).trans_le hH
  have hpow := Real.log_le_log (pow_pos hW0 250) hH
  rw [Real.log_pow] at hpow
  norm_num only [Nat.cast_ofNat] at hpow
  have hlo := Real.log_le_log (div_pos hH0 (pow_pos hW0 10))
    (mrt_arc_long_prefix_quotient_lower hW0 hc hcW hh)
  rw [Real.log_div hH0.ne' (pow_ne_zero 10 hW0.ne'),Real.log_pow] at hlo
  norm_num only [Nat.cast_ofNat] at hlo
  linarith

lemma mrt_arc_long_prefix_prime_ratio {W H Q : ℝ} {h c : ℕ}
    (hW : 0 < W) (hQ : Q ≤ H/W^3)
    (hc : 0 < c) (hcW : (c:ℝ) ≤ W^6)
    (hh : H/W^4 ≤ (h:ℝ)) :
    Q/(h/c+1:ℕ) ≤ W^7 := by
  have hlen := mrt_arc_long_prefix_quotient_lower hW hc hcW hh
  have hlen0 : (0:ℝ) < (h/c+1:ℕ) := by positivity
  apply (div_le_iff₀ hlen0).mpr
  calc
    Q ≤ H/W^3 := hQ
    _ = W^7*(H/W^10) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlen (pow_nonneg hW.le _)

end TwoPointCorrelations

end OAI

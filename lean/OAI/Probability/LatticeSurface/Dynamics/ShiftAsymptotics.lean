import Mathlib

namespace OAI

open Filter

namespace FeasibleShift

lemma scaled_radius_tendsto (C a : ℝ) (ha : a < 1) :
    Tendsto (fun n : ℕ => (C / n) * (n : ℝ)^a) atTop (nhds 0) := by
  have hm := ((tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp only [Function.comp_apply]
  rw [show -(1-a) = a-1 by ring, Real.rpow_sub hn', Real.rpow_one]
  ring

lemma radius_power (n k : ℕ) : ((n : ℝ)^(1/8 : ℝ))^k = (n : ℝ)^((k : ℝ)/8) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1; ring

lemma scaled_radius_sq_tendsto (C : ℝ) :
    Tendsto (fun n : ℕ => (C / n) * ((n : ℝ)^(1/8 : ℝ))^2) atTop (nhds 0) := by
  simp_rw [radius_power]
  exact scaled_radius_tendsto C (2/8) (by norm_num)

lemma tail_radius_bound_tendsto (C : ℝ) :
    Tendsto (fun n : ℕ => C * (n : ℝ)^2 / ((n : ℝ)^(1/8 : ℝ))^32) atTop (nhds 0) := by
  have hm := ((tendsto_rpow_neg_atTop (show (0:ℝ)<2 by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Function.comp_apply]
  rw [radius_power, Real.rpow_neg (by positivity)]
  norm_num only [Nat.cast_ofNat, show (32:ℝ)/8=4 by norm_num, Real.rpow_ofNat]
  field_simp

lemma small_parameter_eventually (D : ℕ) (s₀ s₁ s₂ L C p : ℝ)
    (hs₀ : 0 < s₀) (_hs : s₀ < s₁) (hss : s₁ < s₂) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      (L / n) * (2*(n:ℝ)^(1/8:ℝ)+1) ≤ s₀ ∧
      s₁ + 4*(L/n)*(n:ℝ)^(1/8:ℝ) ≤ s₂ ∧
      (s₁-s₀)⁻¹*(4*D*(L/n))*((n:ℝ)^(1/8:ℝ))^2 ≤ 1/2 ∧
      C * (n:ℝ)^2 / ((n:ℝ)^(1/8:ℝ))^32 ≤ p/4 := by
  have ht1 : Tendsto (fun n : ℕ => (L/n)*(2*(n:ℝ)^(1/8:ℝ)+1)) atTop (nhds 0) := by
    have hh := ((scaled_radius_tendsto L (1/8) (by norm_num)).mul_const 2).add
      (scaled_radius_tendsto L 0 (by norm_num))
    simp only [zero_mul, add_zero, Real.rpow_zero, mul_one] at hh
    convert hh using 1
    ext n; ring
  have ht2 : Tendsto (fun n : ℕ => 4*(L/n)*(n:ℝ)^(1/8:ℝ)) atTop (nhds 0) := by
    have hh := (scaled_radius_tendsto L (1/8) (by norm_num)).const_mul 4
    simpa only [mul_zero, mul_assoc] using hh
  have ht3 : Tendsto (fun n : ℕ => (s₁-s₀)⁻¹*(4*D*(L/n))*((n:ℝ)^(1/8:ℝ))^2) atTop (nhds 0) := by
    convert scaled_radius_sq_tendsto ((s₁-s₀)⁻¹*(4*D*L)) using 1
    ext n; ring
  have ht4 := tail_radius_bound_tendsto C
  filter_upwards [eventually_gt_atTop (0:ℕ), ht1.eventually (eventually_lt_nhds hs₀),
    ht2.eventually (eventually_lt_nhds (sub_pos.mpr hss)),
    ht3.eventually (eventually_lt_nhds (show (0:ℝ)<1/2 by norm_num)),
    ht4.eventually (eventually_lt_nhds (show (0:ℝ)<p/4 by positivity))] with n hn h1 h2 h3 h4
  exact ⟨hn, h1.le, by linarith, h3.le, h4.le⟩

end FeasibleShift

end OAI

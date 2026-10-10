import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEpsilon

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open Asymptotics

lemma one_add_log_rpow_isLittleO (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (fun x : ℝ => (1 + Real.log x) ^ C) =o[atTop] fun x => x ^ δ := by
  let C' := max C 1
  have hC' : 0 < C' := lt_max_iff.mpr (Or.inr zero_lt_one)
  have hq : 0 < δ / C' := div_pos hδ hC'
  have hc : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ (δ / C') := by
    apply (isLittleO_const_left_of_ne one_ne_zero).mpr
    apply (tendsto_rpow_atTop hq).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (Real.norm_of_nonneg (Real.rpow_nonneg hx _)).symm
  have hs := hc.add (isLittleO_log_rpow_atTop hq)
  calc
    (fun x : ℝ => (1 + Real.log x) ^ C) =O[atTop]
        fun x => (1 + Real.log x) ^ C' := by
      apply IsBigO.of_norm_eventuallyLE
      filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx
      simp only [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + Real.log x) C)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    _ =o[atTop] fun x => (x ^ (δ / C')) ^ C' :=
      hs.rpow hC' ((eventually_ge_atTop (0 : ℝ)).mono fun x hx => Real.rpow_nonneg hx _)
    _ =ᶠ[atTop] fun x => x ^ δ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_mul hx,div_mul_cancel₀ _ hC'.ne']

 theorem prefixTemplateFactor_subpower (C : ℝ) {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C ≤ b * (n : ℝ) ^ δ := by
  have h := ((one_add_log_rpow_isLittleO C hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound hb
  filter_upwards [h,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hb0 : 0 ≤ 1 + Real.log (n : ℝ) := by linarith
  simpa only [Function.comp_apply,Real.norm_of_nonneg (Real.rpow_nonneg hb0 C),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) δ),prefixTemplateFactor] using hn

lemma prefixTargetDensity_eq (n : ℕ) :
    prefixTargetDensity n = (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  unfold prefixTargetDensity prefixEpsilon
  congr 1
  norm_num

lemma prefixTargetDensity_tendsto : Tendsto prefixTargetDensity atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => prefixTargetDensity n) atTop (𝓝 0)
  simp_rw [prefixTargetDensity_eq]
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 999 / 2000)).comp
    tendsto_natCast_atTop_atTop

lemma prefixTargetTime_eventually_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ prefixTargetTime n := by
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [prefixTargetDensity_tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    hi.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hp hi
  unfold prefixTargetTime
  exact mul_nonneg (by positivity) (by linarith)

theorem prefixDensity_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (-(999 / 2000 : ℝ)) ≤ prefixDensity n ∧
      prefixDensity n ≤ 2 * (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  filter_upwards [prefixTargetTime_eventually_nonneg,eventually_ge_atTop (6 : ℕ)] with n ht hn
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl,hu⟩ := prefixDensity_bounds n (by omega) ht
  rw [prefixTargetDensity_eq] at hl hu
  refine ⟨hl,?_⟩
  have h1 : 6 / (n : ℝ)^2 ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2) hn0).mpr
    nlinarith
  have h2 : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  linarith

lemma prefix_target_D_identity (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ((n : ℝ) ^ (-(999 / 2000 : ℝ))) ^ 2 =
      (n : ℝ) ^ (1 / 1000 : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← Real.rpow_natCast,← Real.rpow_mul hnR.le]
  conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnR]
  congr 1
  norm_num

theorem prefixD_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (1 / 1000 : ℝ) ≤ prefixD n ∧
      prefixD n ≤ 4 * (n : ℝ) ^ (1 / 1000 : ℝ) := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hp hn
  have hn0 : 0 < n := by omega
  have hq : 0 ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpl : 0 ≤ prefixDensity n := hq.trans hp.1
  rw [← prefix_target_D_identity n hn0]
  unfold prefixD
  constructor
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hp.1 2) (Nat.cast_nonneg n)
  · have hsq := pow_le_pow_left₀ hpl hp.2 2
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hsq)]

lemma prefixDensity_le_one (n : ℕ) : prefixDensity n ≤ 1 := by
  have h₁ : 0 ≤ 1 / (n : ℝ) := by positivity
  have h₂ : 0 ≤ 6 * (prefixTime n : ℝ) / (n : ℝ)^2 := by positivity
  unfold prefixDensity
  linarith

lemma prefix_scales_eventually_pos : ∀ᶠ n : ℕ in atTop,
    0 < prefixDensity n ∧ 1 ≤ prefixD n := by
  filter_upwards [prefixDensity_eventual_envelope,prefixD_eventual_envelope,
    eventually_ge_atTop (1 : ℕ)] with n hp hD hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨(Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < n) _).trans_le hp.1,
    (Real.one_le_rpow hnR (by norm_num : (0 : ℝ) ≤ 1/1000)).trans hD.1⟩

lemma prefix_mixed_power_envelope (k : ℕ) : ∀ᶠ n : ℕ in atTop,
    prefixDensity n * prefixD n ^ k ≤
      (2 * 4 ^ k) * (n : ℝ) ^ (-(999 / 2000 : ℝ) + (k : ℝ) / 1000) := by
  filter_upwards [prefixDensity_eventual_envelope,prefixD_eventual_envelope,
    prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hp hD hpos hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hD0 : 0 ≤ prefixD n := by linarith [hpos.2]
  calc
    _ ≤ (2 * (n : ℝ) ^ (-(999 / 2000 : ℝ))) *
        (4 * (n : ℝ) ^ (1/1000 : ℝ)) ^ k :=
      mul_le_mul hp.2 (pow_le_pow_left₀ hD0 hD.2 k) (pow_nonneg hD0 k) (by positivity)
    _ = _ := by
      rw [mul_pow,← Real.rpow_natCast ((n : ℝ) ^ (1/1000 : ℝ)) k,← Real.rpow_mul hnR.le]
      have he : (1/1000 : ℝ) * k = (k : ℝ) / 1000 := by ring
      rw [he,Real.rpow_add hnR]
      ring

theorem prefixTemplateFactor_mixed_gain (C : ℝ) (k : ℕ)
    (hk : (k : ℝ) / 1000 < 999 / 2000) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C *
      (prefixDensity n * prefixD n ^ k) ≤ 1 := by
  let δ : ℝ := 999/2000 - (k : ℝ)/1000
  have hδ : 0 < δ := sub_pos.mpr hk
  have hK : (0 : ℝ) < 2 * 4 ^ k := by positivity
  filter_upwards [prefixTemplateFactor_subpower C hδ (inv_pos.mpr hK),
    prefix_mixed_power_envelope k,prefix_scales_eventually_pos,
    eventually_ge_atTop (1 : ℕ)] with n hκ hmix hpos hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hb : 0 ≤ prefixDensity n * prefixD n ^ k :=
    mul_nonneg hpos.1.le (pow_nonneg (by linarith [hpos.2]) k)
  calc
    _ ≤ ((2 * 4 ^ k)⁻¹ * (n : ℝ) ^ δ) *
        ((2 * 4 ^ k) * (n : ℝ) ^ (-(999/2000 : ℝ) + (k : ℝ)/1000)) :=
      mul_le_mul hκ hmix hb (by positivity)
    _ = 1 := by
      rw [mul_mul_mul_comm,inv_mul_cancel₀ hK.ne',one_mul,← Real.rpow_add hnR]
      have he : δ + (-(999/2000 : ℝ) + (k : ℝ)/1000) = 0 := by dsimp [δ]; ring
      rw [he,Real.rpow_zero]

theorem prefix_short_suppression (C : ℝ) : ∀ᶠ n : ℕ in atTop,
    prefixTemplateFactor n C * prefixDensity n ≤ (prefixD n ^ 50)⁻¹ := by
  filter_upwards [prefixTemplateFactor_mixed_gain C 50 (by norm_num),
    prefix_scales_eventually_pos] with n hm hp
  have hD : 0 < prefixD n ^ 50 := pow_pos (by linarith [hp.2]) _
  rw [← one_div,(le_div_iff₀ hD)]
  simpa only [mul_assoc] using hm

theorem prefix_suffix_scaling : ∀ᶠ n : ℕ in atTop,
    (n : ℝ)^100 * prefixDensity n ^ 201 ≤ 1 := by
  filter_upwards [prefixTemplateFactor_mixed_gain 0 100 (by norm_num)] with n hn
  simpa only [prefixTemplateFactor,Real.rpow_zero,one_mul,prefixD,mul_pow,
    ← pow_mul,show 201 = 1 + 2 * 100 from rfl,pow_add,pow_one,mul_left_comm] using hn

lemma prefixTemplateFactor_le_D_power (C : ℝ) (k : ℕ) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C ≤ prefixD n ^ k := by
  have he : 0 < (k : ℝ) / 1000 := div_pos (Nat.cast_pos.mpr hk) (by norm_num)
  filter_upwards [prefixTemplateFactor_subpower C he zero_lt_one,
    prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hκ hD hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : ((n : ℝ) ^ (1/1000 : ℝ))^k ≤ prefixD n ^ k :=
    pow_le_pow_left₀ (Real.rpow_nonneg hn0 _) hD.1 _
  have hid : ((n : ℝ) ^ (1/1000 : ℝ))^k = (n : ℝ) ^ ((k : ℝ)/1000) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0]
    congr 1
    ring
  rw [hid] at hm
  apply le_trans _ hm
  simpa only [one_mul] using hκ

theorem prefix_long_suppression (C : ℝ) : ∀ᶠ n : ℕ in atTop,
    prefixTemplateFactor n C ≤ (2 * prefixD n)^100 / prefixD n^50 := by
  filter_upwards [prefixTemplateFactor_le_D_power C 50 (by norm_num),
    prefix_scales_eventually_pos] with n hκ hp
  have hD : 0 < prefixD n := by linarith [hp.2]
  apply (le_div_iff₀ (pow_pos hD 50)).mpr
  calc
    _ ≤ prefixD n^50 * prefixD n^50 := mul_le_mul_of_nonneg_right hκ (by positivity)
    _ = prefixD n^100 := by rw [← pow_add]
    _ ≤ (2 * prefixD n)^100 :=
      pow_le_pow_left₀ hD.le (by linarith) _

end SharpTerminalLeave

end

end OAI

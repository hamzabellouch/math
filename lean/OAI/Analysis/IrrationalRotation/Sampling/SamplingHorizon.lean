import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

namespace Invariant233.SamplingHorizon

open Filter
open scoped Topology

theorem rpow_ratio_le_inv {x a b : ℝ} (hx : 1 ≤ x)
    (hgap : 1 ≤ (b - a) * x) :
    x ^ (a * x) / x ^ (b * x) ≤ x⁻¹ := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [← Real.rpow_sub hxpos, ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le hx
  linarith

theorem horizon_ratio_le_inv {m K : ℝ} (hm : 20 ≤ m)
    (hK : m ^ ((3 / 4 : ℝ) * m) ≤ K) :
    m ^ ((7 / 10 : ℝ) * m) / K ≤ m⁻¹ := by
  have hmpos : 0 < m := by linarith
  have hpowpos : 0 < m ^ ((3 / 4 : ℝ) * m) := Real.rpow_pos_of_pos hmpos _
  calc
    m ^ ((7 / 10 : ℝ) * m) / K ≤
        m ^ ((7 / 10 : ℝ) * m) / m ^ ((3 / 4 : ℝ) * m) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hmpos.le _) hpowpos hK
    _ ≤ m⁻¹ := rpow_ratio_le_inv (by linarith) (by linarith)

theorem decay_le_inv {m : ℝ} (hm : 20 ≤ m) :
    m ^ (-m / 20) ≤ m⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem tendsto_horizon_ratio {m K : ℕ → ℝ}
    (hm : Tendsto m atTop atTop)
    (hK : ∀ n, m n ^ ((3 / 4 : ℝ) * m n) ≤ K n) :
    Tendsto (fun n => m n ^ ((7 / 10 : ℝ) * m n) / K n) atTop (𝓝 0) := by
  have hlarge : ∀ᶠ n in atTop, 20 ≤ m n := hm.eventually_ge_atTop 20
  apply squeeze_zero' _ _ (tendsto_inv_atTop_zero.comp hm)
  · filter_upwards [hlarge] with n hn
    have hpos : 0 < m n := by linarith
    exact div_nonneg (Real.rpow_nonneg hpos.le _)
      (le_trans (Real.rpow_nonneg hpos.le _) (hK n))
  · filter_upwards [hlarge] with n hn
    exact horizon_ratio_le_inv hn (hK n)

theorem tendsto_horizon_ratio_of_pow_two_le {m K : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n)
    (hK : ∀ n, m n ^ ((3 / 4 : ℝ) * m n) ≤ K (n + 1)) :
    Tendsto (fun n => m n ^ ((7 / 10 : ℝ) * m n) / K (n + 1))
      atTop (𝓝 0) := by
  apply tendsto_horizon_ratio _ hK
  exact tendsto_atTop_mono hm (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

theorem ceiling_ratio_le_decay {m : ℝ} (hm : 20 ≤ m) :
    (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) / m ^ ((4 / 5 : ℝ) * m) ≤
      2 * m ^ (-m / 20) := by
  have hmone : 1 ≤ m := by linarith
  have hmpos : 0 < m := by linarith
  have hpowone : 1 ≤ m ^ ((3 / 4 : ℝ) * m) :=
    Real.one_le_rpow hmone (by positivity)
  have hceil : (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤
      2 * m ^ ((3 / 4 : ℝ) * m) := by
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hmpos.le ((3 / 4 : ℝ) * m))
    linarith
  calc
    (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) / m ^ ((4 / 5 : ℝ) * m) ≤
        (2 * m ^ ((3 / 4 : ℝ) * m)) / m ^ ((4 / 5 : ℝ) * m) :=
      div_le_div_of_nonneg_right hceil (Real.rpow_nonneg hmpos.le _)
    _ = 2 * m ^ (((3 / 4 : ℝ) * m) - ((4 / 5 : ℝ) * m)) := by
      rw [Real.rpow_sub hmpos]
      ring
    _ = 2 * m ^ (-m / 20) := by congr 2; ring

theorem ceiling_ratio_le_inv {m : ℝ} (hm : 20 ≤ m) :
    (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) / m ^ ((4 / 5 : ℝ) * m) ≤
      2 * m⁻¹ :=
  (ceiling_ratio_le_decay hm).trans (mul_le_mul_of_nonneg_left (decay_le_inv hm) (by norm_num))

theorem tendsto_ceiling_ratio {m : ℕ → ℝ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => (⌈m n ^ ((3 / 4 : ℝ) * m n)⌉₊ : ℝ) /
      m n ^ ((4 / 5 : ℝ) * m n)) atTop (𝓝 0) := by
  have hlarge : ∀ᶠ n in atTop, 20 ≤ m n := hm.eventually_ge_atTop 20
  have hi : Tendsto (fun n => 2 * (m n)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hm).const_mul 2
  apply squeeze_zero' _ _ hi
  · filter_upwards [hlarge] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
  · filter_upwards [hlarge] with n hn
    exact ceiling_ratio_le_inv hn

theorem eventually_scale_gap {m : ℕ → ℝ} (hm : Tendsto m atTop atTop) (G : ℝ) :
    ∀ᶠ n in atTop, G * (⌈m n ^ ((3 / 4 : ℝ) * m n)⌉₊ : ℝ) <
      m n ^ ((4 / 5 : ℝ) * m n) := by
  have hlim : Tendsto (fun n => G * ((⌈m n ^ ((3 / 4 : ℝ) * m n)⌉₊ : ℝ) /
      m n ^ ((4 / 5 : ℝ) * m n))) atTop (𝓝 0) := by
    simpa using (tendsto_ceiling_ratio hm).const_mul G
  have hlt := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hlt, hm.eventually_ge_atTop 20] with n hn hm20
  have hpow : 0 < m n ^ ((4 / 5 : ℝ) * m n) :=
    Real.rpow_pos_of_pos (by linarith) _
  apply (div_lt_one hpow).mp
  simpa only [mul_div_assoc] using hn

theorem twice_lt_ceiling_cutoff {m : ℝ} (hm : 20 ≤ m) :
    2 * m < (⌈m ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) := by
  have hsq : m ^ 2 ≤ m ^ ((3 / 4 : ℝ) * m) := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ m by linarith) (show (2 : ℝ) ≤ (3 / 4 : ℝ) * m by linarith)
    simpa only [Real.rpow_two] using h
  have hceil := Nat.le_ceil (m ^ ((3 / 4 : ℝ) * m))
  have hstrict : 2 * m < m ^ 2 := by nlinarith
  exact hstrict.trans_le (hsq.trans hceil)

theorem tendsto_ceiling_cutoff {m : ℕ → ℝ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => (⌈m n ^ ((3 / 4 : ℝ) * m n)⌉₊ : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ hm
  filter_upwards [hm.eventually_ge_atTop 20] with n hn
  have h := twice_lt_ceiling_cutoff hn
  linarith

theorem eventually_block_size (B G L H κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, B ≤ (m : ℝ) ∧ 200 ≤ m ∧
      L ≤ κ * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      G * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ ε ∧
      2 * (m : ℝ) < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) := by
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun m : ℕ => κ * (m : ℝ) ^ (1 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hm |>.const_mul_atTop hκ
  have hheight : Tendsto (fun m : ℕ => H /
      (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_ceiling_cutoff hm)).const_mul H
  have hall : ∀ᶠ m : ℕ in atTop, B ≤ (m : ℝ) ∧ 200 ≤ m ∧
      L ≤ κ * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      G * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ ε ∧
      2 * (m : ℝ) < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) := by
    filter_upwards [hm.eventually_ge_atTop B, eventually_ge_atTop 200,
      hpow.eventually_ge_atTop L, eventually_scale_gap hm G,
      hheight.eventually (gt_mem_nhds hε)] with m hB hm200 hL hG hH
    refine ⟨hB, hm200, hL, hG, hH.le, twice_lt_ceiling_cutoff ?_⟩
    exact_mod_cast le_trans (by norm_num : 20 ≤ 200) hm200
  exact hall

theorem exists_block_size (B G L H κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ m : ℕ, B ≤ (m : ℝ) ∧ 200 ≤ m ∧
      L ≤ κ * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      G * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ ε ∧
      2 * (m : ℝ) < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) :=
  (eventually_block_size B G L H κ ε hκ hε).exists

theorem eventually_stage_size (j : ℕ) (hj : 0 < j) (K G Gnext L H d : ℝ) :
    ∀ᶠ m : ℕ in atTop, K ≤ (m : ℝ) ∧ (2 : ℝ) ^ j ≤ m ∧ 4 * G ≤ m ∧ 200 ≤ m ∧
      d ≤ (m : ℝ) / 100 ∧
      L ≤ (1 / (100 * (j : ℝ))) * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      Gnext * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ (1 / 2 : ℝ) ^ j ∧
      2 * K < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hall :=
    eventually_block_size (max K (max ((2 : ℝ) ^ j) (max (4 * G) (100 * d))))
      Gnext L H (1 / (100 * (j : ℝ))) ((1 / 2 : ℝ) ^ j) (by positivity) (by positivity)
  filter_upwards [hall] with m hm
  obtain ⟨hB, hm200, hL, hgap, hH, hdouble⟩ := hm
  simp only [max_le_iff] at hB
  refine ⟨hB.1, hB.2.1, hB.2.2.1, hm200, ?_, hL, hgap, hH, ?_⟩
  · linarith [hB.2.2.2]
  · linarith [hB.1]

theorem exists_stage_size (j : ℕ) (hj : 0 < j) (K G Gnext L H d : ℝ) :
    ∃ m : ℕ, K ≤ (m : ℝ) ∧ (2 : ℝ) ^ j ≤ m ∧ 4 * G ≤ m ∧ 200 ≤ m ∧
      d ≤ (m : ℝ) / 100 ∧
      L ≤ (1 / (100 * (j : ℝ))) * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      Gnext * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ (1 / 2 : ℝ) ^ j ∧
      2 * K < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) :=
  (eventually_stage_size j hj K G Gnext L H d).exists

theorem exists_attenuation (A lower ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ lower ≤ L ∧ A * Real.exp (-L / 10000) ≤ ε := by
  have hm : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ => (n : ℝ) / 10000) atTop atTop :=
    hm.atTop_div_const (by norm_num)
  have hexp : Tendsto (fun n : ℕ => A * Real.exp (-(n : ℝ) / 10000))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, neg_div, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv).const_mul A
  have hall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n ∧ lower ≤ n ∧
      A * Real.exp (-(n : ℝ) / 10000) ≤ ε := by
    filter_upwards [hm.eventually_ge_atTop 1, hm.eventually_ge_atTop lower,
      hexp.eventually (gt_mem_nhds hε)] with n h1 hlo he
    exact ⟨h1, hlo, he.le⟩
  obtain ⟨n, h1, hlo, he⟩ := hall.exists
  exact ⟨n, h1, hlo, he⟩

theorem exists_next_gain (κ L : ℝ) (hκ : 0 < κ) :
    ∃ G : ℕ, 1 ≤ G ∧ L ≤ κ * Real.sqrt (G : ℝ) := by
  have hm : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => κ * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hm).const_mul_atTop hκ
  have hall : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ L ≤ κ * Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, hs.eventually_ge_atTop L] with n hn hL
    exact ⟨hn, hL⟩
  exact hall.exists

end Invariant233.SamplingHorizon

end OAI

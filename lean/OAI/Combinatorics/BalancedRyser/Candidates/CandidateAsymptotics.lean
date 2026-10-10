import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

open Filter
open scoped Topology

namespace Balanced.CandidateAsymptotics

theorem tendsto_ceil_log_mul_ceil_rpow_div {theta beta : ℝ}
    (htheta : 0 ≤ theta) (hgap : theta < beta) :
    Tendsto (fun x : ℝ => (⌈Real.log x⌉₊ : ℝ) * (⌈x ^ theta⌉₊ : ℝ) / x ^ beta)
      atTop (𝓝 0) := by
  have hlog := (isLittleO_log_rpow_atTop (sub_pos.mpr hgap)).tendsto_div_nhds_zero
  have hx : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have hlogone : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  apply squeeze_zero' (hx.mono fun x hx => by positivity)
    (g := fun x : ℝ => 4 * (Real.log x / x ^ (beta - theta)))
  · filter_upwards [hx, hlogone] with x hx hl
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hp : 1 ≤ x ^ theta := Real.one_le_rpow hx htheta
    have hceilLog : (⌈Real.log x⌉₊ : ℝ) ≤ 2 * Real.log x := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ Real.log x by linarith)
      linarith
    have hceilPow : (⌈x ^ theta⌉₊ : ℝ) ≤ 2 * x ^ theta := by
      have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hxpos.le theta)
      linarith
    calc
      (⌈Real.log x⌉₊ : ℝ) * (⌈x ^ theta⌉₊ : ℝ) / x ^ beta ≤
          (2 * Real.log x) * (2 * x ^ theta) / x ^ beta := by gcongr
      _ = 4 * (Real.log x / x ^ (beta - theta)) := by
        rw [Real.rpow_sub hxpos]
        field_simp
        ring
  · simpa using hlog.const_mul (4 : ℝ)

theorem eventually_candidate_numerics : ∀ᶠ q : ℕ in atTop,
    let P := Nat.ceil ((q : ℝ) ^ (1 / 100 : ℝ))
    let B := Nat.ceil (Real.log (q : ℝ))
    let R := 6 * P + 16 * B * P
    (((2 + 4 * P : ℕ) : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
    (((4 + P + R : ℕ) : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
    (((48 + 10 * P + 2 * R : ℕ) : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
    (((8 * (q + 1) + R : ℕ) : ℝ) ≤ 10 * q) := by
  have hlim := (tendsto_ceil_log_mul_ceil_rpow_div
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1 / 8)).comp
      tendsto_natCast_atTop_atTop
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 102))
  have hlogone : ∀ᶠ q : ℕ in atTop, 1 ≤ Real.log (q : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hsmall, hlogone, eventually_ge_atTop 8] with q hsmall hlog hq
  dsimp only
  let P : ℝ := Nat.ceil ((q : ℝ) ^ (1 / 100 : ℝ))
  let B : ℝ := Nat.ceil (Real.log (q : ℝ))
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hqone
  have hP : 1 ≤ P := (Real.one_le_rpow hqone (by norm_num : (0 : ℝ) ≤ 1 / 100)).trans
    (Nat.le_ceil _)
  have hB : 1 ≤ B := hlog.trans (Nat.le_ceil _)
  have hBP : 1 ≤ B * P := by nlinarith
  have hPBP : P ≤ B * P := by nlinarith
  have hpowerpos : 0 < (q : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hqpos _
  have hbig : 102 * (B * P) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := by
    have h := (div_lt_iff₀ hpowerpos).mp hsmall
    change B * P < (1 / 102 : ℝ) * (q : ℝ) ^ (1 / 8 : ℝ) at h
    linarith
  have hpowq : (q : ℝ) ^ (1 / 8 : ℝ) ≤ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hqone (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hq8 : (8 : ℝ) ≤ q := by exact_mod_cast hq
  push_cast
  change (2 + 4 * P ≤ _) ∧ (4 + P + (6 * P + 16 * B * P) ≤ _) ∧
    (48 + 10 * P + 2 * (6 * P + 16 * B * P) ≤ _) ∧
    (8 * ((q : ℝ) + 1) + (6 * P + 16 * B * P) ≤ _)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem eventually_scaled_product_le (C : ℝ) : ∀ᶠ q : ℕ in atTop,
    C * (⌈Real.log (q : ℝ)⌉₊ : ℝ) * (⌈(q : ℝ) ^ (1 / 100 : ℝ)⌉₊ : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hlim := ((tendsto_ceil_log_mul_ceil_rpow_div
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1 / 8)).comp
      tendsto_natCast_atTop_atTop).const_mul C
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : C * (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop 1] with q hsmall hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpos : 0 < (q : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hqpos _
  have hdiv : (C * (⌈Real.log (q : ℝ)⌉₊ : ℝ) *
      (⌈(q : ℝ) ^ (1 / 100 : ℝ)⌉₊ : ℝ)) / (q : ℝ) ^ (1 / 8 : ℝ) < 1 := by
    simpa only [Function.comp_apply, mul_div_assoc, mul_assoc] using hsmall
  exact ((div_lt_iff₀ hpos).mp hdiv).le.trans_eq (one_mul _)

end Balanced.CandidateAsymptotics

end OAI

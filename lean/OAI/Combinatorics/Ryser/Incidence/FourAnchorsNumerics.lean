import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem fourAnchors_degree_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) :
    2 ≤ r / (8 * U ^ 2) := by
  let _ := hr
  have hUpos : 0 < U := by linarith
  have hUone : 1 ≤ U := by linarith
  have hpow : U ^ 2 ≤ U ^ 7 := pow_le_pow_right₀ hUone (by norm_num)
  apply (le_div_iff₀ (show 0 < 8 * U ^ 2 by positivity)).mpr
  nlinarith only [hrlarge, hpow, sq_nonneg U]

theorem fourAnchors_pair_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) :
    r ^ 2 / (128 * U ^ 4) ≤
      (r / (8 * U ^ 2)) * (r / (8 * U ^ 2) - 1) := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  let d : ℝ := r / (8 * U ^ 2)
  have hd : 2 ≤ d := fourAnchors_degree_lower hr hU hrlarge
  have hd0 : 0 ≤ d := by linarith
  have hd2 : 0 ≤ d - 2 := by linarith
  have hid : r ^ 2 / (128 * U ^ 4) = d ^ 2 / 2 := by
    dsimp [d]
    field_simp [hUne]; ring
  change r ^ 2 / (128 * U ^ 4) ≤ d * (d - 1)
  rw [hid]
  nlinarith only [mul_nonneg hd0 hd2]

theorem fourAnchors_surplus_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) {N : ℝ}
    (hN : r ^ 2 / (128 * U ^ 4) ≤ N) :
    r ^ 3 / (2048 * U ^ 6) ≤
      (r / (8 * U ^ 2)) * N - 2 * (U * r ^ 2) := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  have hcost : 2 * (U * r ^ 2) ≤ r ^ 3 / (2048 * U ^ 6) := by
    apply (le_div_iff₀ (show 0 < 2048 * U ^ 6 by positivity)).mpr
    calc
      2 * (U * r ^ 2) * (2048 * U ^ 6) = (4096 * U ^ 7) * r ^ 2 := by ring
      _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_right hrlarge (sq_nonneg r)
      _ = r ^ 3 := by ring
  have hmain : (r / (8 * U ^ 2)) * (r ^ 2 / (128 * U ^ 4)) ≤
      (r / (8 * U ^ 2)) * N :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have hid : (r / (8 * U ^ 2)) * (r ^ 2 / (128 * U ^ 4)) =
      2 * (r ^ 3 / (2048 * U ^ 6)) := by
    field_simp [hUne]; ring
  nlinarith only [hcost, hmain, hid]

theorem fourAnchors_margin_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) :
    r ^ 2 / (256 * U ^ 4) ≤
      r ^ 2 / (128 * U ^ 4) - 16 * U ^ 3 * r := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  have hcost : 16 * U ^ 3 * r ≤ r ^ 2 / (256 * U ^ 4) := by
    apply (le_div_iff₀ (show 0 < 256 * U ^ 4 by positivity)).mpr
    calc
      (16 * U ^ 3 * r) * (256 * U ^ 4) = (4096 * U ^ 7) * r := by ring
      _ ≤ r * r := mul_le_mul_of_nonneg_right hrlarge hr.le
      _ = r ^ 2 := by ring
  have hid : r ^ 2 / (128 * U ^ 4) = 2 * (r ^ 2 / (256 * U ^ 4)) := by
    field_simp [hUne]; ring
  linarith only [hcost, hid]

theorem fourAnchors_count_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) {N L T : ℝ}
    (hN : r ^ 2 / (128 * U ^ 4) ≤ N)
    (hL0 : 0 ≤ L) (hL : L ≤ U * r ^ 2) (hT0 : 0 ≤ T)
    (hcount : (2 / 9 : ℝ) *
      ((r / (8 * U ^ 2)) * N - 2 * (U * r ^ 2)) ^ 3 ≤ L ^ 2 * T) :
    r ^ 5 / (9 * 2 ^ 32 * U ^ 20) ≤ T := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  let a : ℝ := r ^ 3 / (2048 * U ^ 6)
  let k : ℝ := r ^ 5 / (9 * 2 ^ 32 * U ^ 20)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hsurplus : a ≤ (r / (8 * U ^ 2)) * N - 2 * (U * r ^ 2) :=
    fourAnchors_surplus_lower hr hU hrlarge hN
  have hcube := pow_le_pow_left₀ ha0 hsurplus 3
  have hLsq : L ^ 2 ≤ (U * r ^ 2) ^ 2 := pow_le_pow_left₀ hL0 hL 2
  have hbound : (2 / 9 : ℝ) * a ^ 3 ≤ (U * r ^ 2) ^ 2 * T := by
    calc
      (2 / 9 : ℝ) * a ^ 3 ≤ (2 / 9 : ℝ) *
          ((r / (8 * U ^ 2)) * N - 2 * (U * r ^ 2)) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (by norm_num)
      _ ≤ L ^ 2 * T := hcount
      _ ≤ (U * r ^ 2) ^ 2 * T := mul_le_mul_of_nonneg_right hLsq hT0
  have hid : (U * r ^ 2) ^ 2 * k = (2 / 9 : ℝ) * a ^ 3 := by
    dsimp [k, a]
    field_simp [hUne]; ring
  change k ≤ T
  apply (mul_le_mul_iff_right₀ (show 0 < (U * r ^ 2) ^ 2 by positivity)).mp
  rw [hid]
  exact hbound

theorem fourAnchors_total_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    {P extra T total : ℝ}
    (hP : r ^ 2 / (32 * U ^ 4) ≤ P)
    (hExtra : r ^ 2 / (256 * U ^ 4) ≤ extra)
    (hT : r ^ 5 / (9 * 2 ^ 32 * U ^ 20) ≤ T)
    (hTotal : P * extra * T ≤ total) :
    r ^ 9 / (9 * 2 ^ 45 * U ^ 28) ≤ total := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  have hp0 : 0 ≤ r ^ 2 / (32 * U ^ 4) := by positivity
  have he0 : 0 ≤ r ^ 2 / (256 * U ^ 4) := by positivity
  have ht0 : 0 ≤ r ^ 5 / (9 * 2 ^ 32 * U ^ 20) := by positivity
  have hP0 : 0 ≤ P := hp0.trans hP
  have hExtra0 : 0 ≤ extra := he0.trans hExtra
  have hproduct :
      (r ^ 2 / (32 * U ^ 4)) * (r ^ 2 / (256 * U ^ 4)) *
          (r ^ 5 / (9 * 2 ^ 32 * U ^ 20)) ≤ P * extra * T :=
    mul_le_mul (mul_le_mul hP hExtra he0 hP0) hT ht0 (mul_nonneg hP0 hExtra0)
  calc
    r ^ 9 / (9 * 2 ^ 45 * U ^ 28) =
        (r ^ 2 / (32 * U ^ 4)) * (r ^ 2 / (256 * U ^ 4)) *
          (r ^ 5 / (9 * 2 ^ 32 * U ^ 20)) := by
      field_simp [hUne]; ring
    _ ≤ P * extra * T := hproduct
    _ ≤ total := hTotal

theorem fourAnchors_candidate_upper {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    {L P : ℝ} (_hL0 : 0 ≤ L) (hL : L ≤ U * r ^ 2)
    (hP0 : 0 ≤ P) (hP : P ≤ U * r ^ 2) :
    L * (16 * U ^ 3 * r) ^ 3 * P ≤ 2 ^ 12 * U ^ 11 * r ^ 7 := by
  have hUpos : 0 < U := by linarith
  have hcap0 : 0 ≤ (16 * U ^ 3 * r) ^ 3 := by positivity
  have hM0 : 0 ≤ U * r ^ 2 := by positivity
  calc
    L * (16 * U ^ 3 * r) ^ 3 * P ≤
        (U * r ^ 2) * (16 * U ^ 3 * r) ^ 3 * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hcap0) hP0
    _ ≤ (U * r ^ 2) * (16 * U ^ 3 * r) ^ 3 * (U * r ^ 2) :=
      mul_le_mul_of_nonneg_left hP (mul_nonneg hM0 hcap0)
    _ = 2 ^ 12 * U ^ 11 * r ^ 7 := by ring

theorem fourAnchors_average_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    {total candidate W : ℝ}
    (hTotal : r ^ 9 / (9 * 2 ^ 45 * U ^ 28) ≤ total)
    (hCandidate : candidate ≤ 2 ^ 12 * U ^ 11 * r ^ 7)
    (hW : 0 ≤ W) (hLink : total ≤ candidate * W) :
    r ^ 2 / (9 * 2 ^ 57 * U ^ 39) ≤ W := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  have hcap : 0 < 2 ^ 12 * U ^ 11 * r ^ 7 := by positivity
  apply (mul_le_mul_iff_right₀ hcap).mp
  calc
    (2 ^ 12 * U ^ 11 * r ^ 7) * (r ^ 2 / (9 * 2 ^ 57 * U ^ 39)) =
        r ^ 9 / (9 * 2 ^ 45 * U ^ 28) := by
      field_simp [hUne]
    _ ≤ total := hTotal
    _ ≤ candidate * W := hLink
    _ ≤ (2 ^ 12 * U ^ 11 * r ^ 7) * W := mul_le_mul_of_nonneg_right hCandidate hW

end RyserCoveringCounterexample.Incidence

end OAI

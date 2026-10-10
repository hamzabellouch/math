import OAI.NumberTheory.Jacobsthal.Primes.PrimeBinCounting

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosTagSubbins

noncomputable def count (w Cs : ℝ) : ℕ := ⌈w ^ (2 * Cs + 10)⌉₊
noncomputable def step (R theta : ℝ) (N : ℕ) : ℝ := R * theta / N
noncomputable def left (R theta : ℝ) (N i : ℕ) : ℝ := R + i * step R theta N
noncomputable def right (R theta : ℝ) (N i : ℕ) : ℝ := R + (i + 1 : ℕ) * step R theta N
noncomputable def width (R theta : ℝ) (N i : ℕ) : ℝ := step R theta N / left R theta N i

theorem count_bounds {w Cs : ℝ} (hw : 1 < w) (hCs : 0 ≤ Cs) :
    1 ≤ count w Cs ∧ w ^ (2 * Cs + 10) ≤ (count w Cs : ℝ) ∧
    (count w Cs : ℝ) ≤ 2 * w ^ (2 * Cs + 10) := by
  have hp : 1 ≤ w ^ (2 * Cs + 10) := Real.one_le_rpow hw.le (by linarith)
  refine ⟨Nat.one_le_ceil_iff.mpr (by linarith), Nat.le_ceil _, ?_⟩
  have h := Nat.ceil_lt_add_one (le_trans (by norm_num) hp)
  dsimp [count]
  linarith

theorem step_pos {R theta : ℝ} {N : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : 0 < step R theta N := by unfold step; positivity

theorem left_lower {R theta : ℝ} {N i : ℕ} (hs : 0 ≤ step R theta N) :
    R ≤ left R theta N i := by unfold left; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hs)

theorem right_sub_left (R theta : ℝ) (N i : ℕ) :
    right R theta N i - left R theta N i = step R theta N := by
  simp only [right, left, Nat.cast_add, Nat.cast_one]; ring

theorem right_eq_left_add (R theta : ℝ) (N i : ℕ) :
    right R theta N i = left R theta N i + step R theta N := by
  linarith [right_sub_left R theta N i]

theorem total_step {R theta : ℝ} {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * step R theta N = R * theta := by
  unfold step; field_simp

theorem right_upper {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hi : i < N) : right R theta N i ≤ (1 + theta) * R := by
  have hN : 0 < N := Nat.zero_lt_of_lt hi
  have hs := step_pos hR ht hN
  have hi' : ((i + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hi
  have h := mul_le_mul_of_nonneg_right hi' hs.le
  rw [total_step hN] at h
  dsimp [right]; nlinarith only [h]

theorem left_pos {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : 0 < left R theta N i :=
  hR.trans_le (left_lower (step_pos hR ht hN).le)

theorem left_lt_right {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : left R theta N i < right R theta N i := by
  rw [right_eq_left_add]; linarith [step_pos hR ht hN]

theorem width_pos {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : 0 < width R theta N i :=
  div_pos (step_pos hR ht hN) (left_pos hR ht hN)

theorem local_endpoint {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : (1 + width R theta N i) * left R theta N i = right R theta N i := by
  have hl := ne_of_gt (left_pos (i := i) hR ht hN)
  rw [width, add_mul, one_mul, div_mul_cancel₀ _ hl, right_eq_left_add]

theorem endpoints_ordered {R theta : ℝ} {N i j : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) (hij : i < j) : right R theta N i ≤ left R theta N j := by
  have hij' : ((i + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hij
  unfold right left
  exact add_le_add_right (mul_le_mul_of_nonneg_right hij' (step_pos hR ht hN).le) R

theorem exists_unique_index {R theta x : ℝ} {N : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) (hx : R < x) (hx' : x ≤ (1 + theta) * R) :
    ∃! i : Fin N, left R theta N i < x ∧ x ≤ right R theta N i := by
  let u := (x - R) / step R theta N
  have hs := step_pos hR ht hN
  have hu : 0 < u := div_pos (sub_pos.mpr hx) hs
  have hceil : 1 ≤ ⌈u⌉₊ := Nat.one_le_ceil_iff.mpr hu
  have huN : u ≤ N := by
    apply (div_le_iff₀ hs).mpr
    rw [total_step hN]
    nlinarith only [hx']
  have hkN : ⌈u⌉₊ ≤ N := Nat.ceil_le.mpr huN
  let i : Fin N := ⟨⌈u⌉₊ - 1, by omega⟩
  have hki : (i : ℕ) + 1 = ⌈u⌉₊ := by dsimp [i]; omega
  have hceil0 : ⌈u⌉₊ ≠ 0 := by omega
  have hlo := ((Nat.ceil_eq_iff hceil0).mp rfl).1
  have hhi := Nat.le_ceil u
  have himem : left R theta N i < x ∧ x ≤ right R theta N i := by
    constructor
    · have h := (lt_div_iff₀ hs).mp hlo
      change R + (↑(⌈u⌉₊ - 1) : ℝ) * step R theta N < x
      linarith only [h]
    · have h := (div_le_iff₀ hs).mp hhi
      dsimp [right]
      rw [hki]
      linarith only [h]
  refine ⟨i, himem, ?_⟩
  intro j hj
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjlt | hilt
  · have h := endpoints_ordered hR ht hN hjlt
    linarith only [h, himem.1, hj.2]
  · have h := endpoints_ordered hR ht hN hilt
    linarith only [h, himem.2, hj.1]

end ErdosTagSubbins

end

section

namespace ErdosTagSubbins

theorem width_le_theta_div {R theta : ℝ} {N i : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) : width R theta N i ≤ theta / N := by
  have hl := left_lower (i := i) (step_pos hR ht hN).le
  have hs := step_pos hR ht hN
  calc
    width R theta N i ≤ step R theta N / R := div_le_div_of_nonneg_left hs.le hR hl
    _ = theta / N := by unfold step; field_simp

theorem width_upper {R theta w Cs : ℝ} {i : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hw : 1 < w) (hCs : 0 ≤ Cs) :
    width R theta (count w Cs) i ≤ w ^ (-2 * Cs - 10) := by
  have hb := count_bounds hw hCs
  have hN : 0 < count w Cs := hb.1
  have hq : 0 < w ^ (2 * Cs + 10) := Real.rpow_pos_of_pos (by linarith) _
  calc
    _ ≤ theta / (count w Cs : ℝ) := width_le_theta_div hR ht hN
    _ ≤ 1 / (count w Cs : ℝ) := div_le_div_of_nonneg_right ht1 (by positivity)
    _ ≤ 1 / w ^ (2 * Cs + 10) := div_le_div_of_nonneg_left (by norm_num) hq hb.2.1
    _ = w ^ (-2 * Cs - 10) := by
      rw [show -2 * Cs - 10 = -(2 * Cs + 10) by ring, Real.rpow_neg (by linarith : 0 ≤ w)]
      exact one_div _

theorem width_lower {R theta w Cs xi : ℝ} {i : ℕ} (hR : 0 < R)
    (hxi : 0 < xi) (htxi : xi / 4 ≤ theta) (ht1 : theta ≤ 1)
    (hw : 1 < w) (hCs : 0 ≤ Cs) (hi : i < count w Cs) :
    xi / (16 * w ^ (2 * Cs + 10)) ≤ width R theta (count w Cs) i := by
  have ht : 0 < theta := (div_pos hxi (by norm_num)).trans_le htxi
  have hb := count_bounds hw hCs
  have hN : 0 < count w Cs := hb.1
  have hNr : (0 : ℝ) < count w Cs := by exact_mod_cast hN
  have hq : 0 < w ^ (2 * Cs + 10) := Real.rpow_pos_of_pos (by linarith) _
  have hl := left_pos (i := i) hR ht hN
  have hlu : left R theta (count w Cs) i ≤ 2 * R := by
    have h := (left_lt_right (i := i) hR ht hN).le.trans (right_upper hR ht hi)
    nlinarith only [h, mul_le_mul_of_nonneg_right ht1 hR.le]
  calc
    xi / (16 * w ^ (2 * Cs + 10)) ≤ theta / (4 * w ^ (2 * Cs + 10)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h := mul_le_mul_of_nonneg_right htxi (show 0 ≤ 16 * w ^ (2 * Cs + 10) by positivity)
      nlinarith only [h]
    _ ≤ theta / (2 * (count w Cs : ℝ)) := by
      apply div_le_div_of_nonneg_left ht.le (by positivity)
      linarith only [hb.2.2]
    _ = step R theta (count w Cs) / (2 * R) := by unfold step; field_simp
    _ ≤ width R theta (count w Cs) i := div_le_div_of_nonneg_left
      (step_pos hR ht hN).le hl hlu

theorem local_common_interval_geometry {R theta w Cs : ℝ} {i : ℕ}
    (hR : 0 < R) (ht : 0 < theta) (ht1 : theta ≤ 1) (hw : 1 < w)
    (hCs : 0 ≤ Cs) (hi : i < count w Cs) :
    0 < left R theta (count w Cs) i ∧
    left R theta (count w Cs) i < right R theta (count w Cs) i ∧
    right R theta (count w Cs) i ≤
      (1 + w ^ (-2 * Cs - 10)) * left R theta (count w Cs) i ∧
    right R theta (count w Cs) i ≤ (1 + theta) * R := by
  have hN : 0 < count w Cs := (count_bounds hw hCs).1
  have hl := left_pos (i := i) hR ht hN
  refine ⟨hl, left_lt_right hR ht hN, ?_, right_upper hR ht hi⟩
  rw [← local_endpoint hR ht hN]
  exact mul_le_mul_of_nonneg_right (add_le_add_right (width_upper hR ht ht1 hw hCs) 1) hl.le

end ErdosTagSubbins

end

end Erdos970

end OAI

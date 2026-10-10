import OAI.Combinatorics.CliqueFree.Model

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

lemma log_bounds {x : ℝ} (hx : 32 ≤ x) : 1 ≤ Real.log x ∧ 7 * Real.log x ≤ x := by
  have hx0 : 0 < x := by linarith
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlower := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ x by linarith)
  rw [h4] at hlower
  have hupper := Real.log_le_sub_one_of_pos (div_pos hx0 (by norm_num : (0 : ℝ) < 32))
  rw [Real.log_div hx0.ne' (by norm_num), h32] at hupper
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  constructor <;> linarith

lemma pow_six_le_exp {x : ℝ} (hx : 32 ≤ x) : x ^ 6 ≤ Real.exp x := by
  have hx0 : 0 < x := by linarith
  have hlog := log_bounds hx
  calc
    _ = Real.exp (6 * Real.log x) := by
      have hp : Real.log (x ^ 6) = 6 * Real.log x := by simp only [Real.log_pow, Nat.cast_ofNat]
      rw [← hp, Real.exp_log (pow_pos hx0 6)]
    _ ≤ _ := Real.exp_le_exp.2 (by linarith)

lemma exp_neg_le_inv_pow_seven {x : ℝ} (hx : 32 ≤ x) :
    Real.exp (-x) ≤ 1 / x ^ 7 := by
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ Real.exp (-(7 * Real.log x)) := Real.exp_le_exp.2 (by linarith [(log_bounds hx).2])
    _ = _ := by
      have hp : Real.log (x ^ 7) = 7 * Real.log x := by simp only [Real.log_pow, Nat.cast_ofNat]
      rw [Real.exp_neg, ← hp, Real.exp_log (pow_pos hx0 7)]
      simp only [one_div]

noncomputable def threshold (x : ℝ) : ℝ := 1 / (Real.exp x * x ^ 6)

lemma threshold_pos {x : ℝ} (hx : 0 < x) : 0 < threshold x :=
  one_div_pos.2 (mul_pos (Real.exp_pos x) (pow_pos hx 6))

lemma growth_factor_le {x : ℝ} (hx : 32 ≤ x) :
    1 + Real.exp x / threshold x ≤ Real.exp (4 * x) := by
  have hx0 : 0 ≤ x := by linarith
  have he1 : 1 ≤ Real.exp x := Real.one_le_exp_iff.2 hx0
  have he2 : 2 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hp3 : 1 ≤ Real.exp x ^ 3 := one_le_pow₀ he1
  have hid : Real.exp x / threshold x = Real.exp x * Real.exp x * x ^ 6 := by
    unfold threshold
    simp only [div_div_eq_mul_div, div_one]
    ring
  rw [hid, show 4 * x = (4 : ℕ) * x by norm_num, Real.exp_nat_mul]
  calc
    _ ≤ 1 + Real.exp x * Real.exp x * Real.exp x :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_six_le_exp hx) (by positivity))
    _ = 1 + Real.exp x ^ 3 := by ring
    _ ≤ 2 * Real.exp x ^ 3 := by linarith
    _ ≤ Real.exp x * Real.exp x ^ 3 := mul_le_mul_of_nonneg_right he2 (by positivity)
    _ = _ := by ring

lemma leakage_factor {x : ℝ} (hx : 0 < x) :
    x ^ 2 * threshold x * Real.exp x = 1 / x ^ 4 := by
  unfold threshold
  field_simp [hx.ne', (Real.exp_pos x).ne']

lemma ceil_bounds {x : ℝ} (hx : 32 ≤ x) :
    0 < ⌈x⌉₊ ∧ x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have hl := Nat.le_ceil x
  have hu := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  refine ⟨?_, hl, by linarith⟩
  have : (0 : ℝ) < (⌈x⌉₊ : ℝ) := by linarith
  exact_mod_cast this

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

def lossRatio (x : ℝ) : ℝ := Real.log x / Real.sqrt x

def scale (X : ℝ) : ℕ → ℝ
  | 0 => X
  | n+1 => (scale X n)^2

lemma scale_ge {X : ℝ} (hX : 1 ≤ X) (n : ℕ) : X ≤ scale X n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 1 ≤ scale X n := hX.trans ih
    dsimp [scale]
    nlinarith

lemma scale_ge_add {X : ℝ} (hX : 2 ≤ X) (n : ℕ) : X + n ≤ scale X n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 2 ≤ scale X n := hX.trans (scale_ge (by linarith) n)
    simp only [scale, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma lossRatio_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lossRatio x :=
  div_nonneg (Real.log_nonneg hx) (Real.sqrt_nonneg _)

lemma lossRatio_square {x : ℝ} (hx : 16 ≤ x) : lossRatio (x^2) ≤ (1/2) * lossRatio x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq := Real.sq_sqrt hx0.le
  have hs0 := Real.sqrt_nonneg x
  have hs : 4 ≤ Real.sqrt x := by nlinarith
  unfold lossRatio
  rw [Real.log_pow, Real.sqrt_sq hx0.le]
  norm_num only [Nat.cast_ofNat]
  apply (div_le_iff₀ hx0).2
  rw [mul_assoc, div_mul_eq_mul_div]
  have hid : (Real.log x * x) / Real.sqrt x = Real.log x * Real.sqrt x := by
    apply (div_eq_iff (by linarith : Real.sqrt x ≠ 0)).2
    nlinarith
  have hid' : Real.log x / Real.sqrt x * x = Real.log x * Real.sqrt x := by
    calc
      _ = Real.log x * x / Real.sqrt x := by ring
      _ = _ := hid
  rw [hid']
  nlinarith [mul_le_mul_of_nonneg_left hs hl]

lemma lossRatio_scale {X : ℝ} (hX : 16 ≤ X) (n : ℕ) :
    lossRatio (scale X n) ≤ (1/2 : ℝ)^n * lossRatio X := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 16 ≤ scale X n := hX.trans (scale_ge (by linarith) n)
    calc
      _ ≤ (1/2) * lossRatio (scale X n) := lossRatio_square ht
      _ ≤ (1/2) * ((1/2 : ℝ)^n * lossRatio X) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

lemma inv_scale {X : ℝ} (hX : 2 ≤ X) (n : ℕ) :
    1 / scale X n ≤ (1/2 : ℝ)^n * (1/X) := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 2 ≤ scale X n := hX.trans (scale_ge (by linarith) n)
    have ht0 : 0 < scale X n := by linarith
    have he : 1 / (scale X n)^2 ≤ (1/2) * (1 / scale X n) := by
      apply (div_le_iff₀ (pow_pos ht0 2)).2
      field_simp
      nlinarith
    calc
      _ ≤ (1/2) * (1 / scale X n) := he
      _ ≤ (1/2) * ((1/2 : ℝ)^n * (1/X)) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

lemma exists_iteration_threshold (a : ℝ) :
    ∃ X : ℝ, 32 ≤ X ∧ a * lossRatio X ≤ 1/4 := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  have ht : Tendsto (fun x : ℝ ↦ a * lossRatio x) atTop (nhds 0) := by
    simpa only [lossRatio, Real.sqrt_eq_rpow, mul_zero] using h.const_mul a
  have he : ∀ᶠ x : ℝ in atTop, a * lossRatio x < 1/4 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨X,hX⟩ := eventually_atTop.1 he
  exact ⟨max 32 X, le_max_left _ _, (hX (max 32 X) (le_max_right _ _)).le⟩

lemma recurrence_bound {B q ε t m s : ℝ}
    (hB : 1 ≤ B) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (_hε0 : 0 ≤ ε) (hε : ε ≤ q/4) (_ht : 0 ≤ t) (hm : 0 ≤ m)
    (hs : s ≤ q/2)
    (hstep : (1-ε)*t - s*m ≤ B*(2-2*q)*m) :
    t ≤ B*(2-q)*m := by
  have hB0 : 0 ≤ B := by linarith
  have hb : 0 ≤ B*(2-q) := mul_nonneg hB0 (by linarith)
  have hb2 : B*(2-q) ≤ 2*B := by nlinarith
  have hnum : B*(2-2*q)+s ≤ (1-ε)*(B*(2-q)) := by
    have he : ε * (B*(2-q)) ≤ (q/4)*(2*B) :=
      mul_le_mul hε hb2 hb (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 hB) hq0]
  have hpos : 0 < 1-ε := by linarith
  apply (mul_le_mul_iff_right₀ hpos).1
  have hh := mul_le_mul_of_nonneg_right hnum hm
  nlinarith only [hh,hstep]

end CliqueFreeIndependence.Numerical

end

end OAI

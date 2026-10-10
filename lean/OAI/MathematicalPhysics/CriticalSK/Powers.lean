import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

lemma rpow_three_eighth_sub_le {s x y : ℝ} (hs : 0 < s) (hsx : s ≤ x) (hxy : x ≤ y) :
    y ^ (3 / 8 : ℝ) - x ^ (3 / 8 : ℝ) ≤
      (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) * (y - x) := by
  have hx : 0 < x := hs.trans_le hsx
  have hd (z : ℝ) (hz : z ∈ Set.Icc x y) :
      HasDerivWithinAt (fun z : ℝ => z ^ (3 / 8 : ℝ))
        ((3 / 8 : ℝ) * z ^ (-5 / 8 : ℝ)) (Set.Icc x y) z := by
    have h := (Real.hasDerivAt_rpow_const (p := (3 / 8 : ℝ))
      (Or.inl (ne_of_gt (hx.trans_le hz.1)))).hasDerivWithinAt (s := Set.Icc x y)
    norm_num at h ⊢
    exact h
  have hb (z : ℝ) (hz : z ∈ Set.Ico x y) :
      ‖(3 / 8 : ℝ) * z ^ (-5 / 8 : ℝ)‖ ≤ (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) := by
    have hz0 : 0 ≤ z := (hx.trans_le hz.1).le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (3 / 8 : ℝ) * z ^ (-5 / 8 : ℝ))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs (hsx.trans hz.1) (by norm_num)) (by norm_num)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb y ⟨hxy, le_rfl⟩
  exact (le_abs_self _).trans h

lemma rpow_three_eighth_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ (3 / 8 : ℝ) ≤ y ^ (3 / 8 : ℝ) := Real.rpow_le_rpow hx hxy (by norm_num)

def edgeError (A B C s e : ℝ) : ℝ := A * (e + s) ^ (3 / 8 : ℝ) + B + C * e

lemma edgeError_mono {A B C s : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 < s) :
    MonotoneOn (edgeError A B C s) (Set.Ici 0) := by
  intro x hx y _hy hxy
  change 0 ≤ x at hx
  dsimp [edgeError]
  gcongr

lemma edgeError_increment {A B C s x y : ℝ} (hA : 0 ≤ A) (hs : 0 < s)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    edgeError A B C s y - edgeError A B C s x ≤
      (A * (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) + C) * (y - x) := by
  have h := mul_le_mul_of_nonneg_left (rpow_three_eighth_sub_le hs
    (show s ≤ x + s by linarith) (show x + s ≤ y + s by linarith)) hA
  dsimp [edgeError]
  nlinarith

lemma edgeError_gap_comparison_mono {A B C s : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 < s)
    (hsmall : A * (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) + C ≤ 1) :
    MonotoneOn (fun e => e + edgeError A B C s e) (Set.Ici 0) ∧
    MonotoneOn (fun e => e - edgeError A B C s e) (Set.Ici 0) := by
  constructor
  · intro x hx y hy hxy
    have := edgeError_mono (B := B) hA hC hs hx hy hxy
    linarith
  · intro x hx y _hy hxy
    have h := edgeError_increment (B := B) (C := C) hA hs hx hxy
    have h' := mul_le_mul_of_nonneg_right hsmall (sub_nonneg.mpr hxy)
    linarith

lemma edgeError_eigenvalue_comparison_mono {A B C s : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 < s)
    (hsmall : A * (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) + C ≤ 1) :
    MonotoneOn (fun v => v + edgeError A B C s (2 - v)) (Set.Iic 2) ∧
    MonotoneOn (fun v => v - edgeError A B C s (2 - v)) (Set.Iic 2) := by
  obtain ⟨hp, hm⟩ := edgeError_gap_comparison_mono (B := B) hA hC hs hsmall
  constructor
  · intro x hx y hy hxy
    have h := hm (show 0 ≤ 2 - y by exact sub_nonneg.mpr hy)
      (show 0 ≤ 2 - x by exact sub_nonneg.mpr hx) (by linarith : 2 - y ≤ 2 - x)
    linarith
  · intro x hx y hy hxy
    have h := hp (show 0 ≤ 2 - y by exact sub_nonneg.mpr hy)
      (show 0 ≤ 2 - x by exact sub_nonneg.mpr hx) (by linarith : 2 - y ≤ 2 - x)
    linarith

lemma edgeError_relative {A B C s t e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hs : 0 < s) (hst : s ≤ t) (he : 0 ≤ e) :
    edgeError A B C s e ≤ (A * s ^ (-5 / 8 : ℝ) + B / s + C) * (t + e) := by
  have hes : 0 < e + s := by linarith
  have ht : 0 < t + e := by linarith
  have hp : (e + s) ^ (3 / 8 : ℝ) = (e + s) * (e + s) ^ (-5 / 8 : ℝ) := by
    nth_rw 2 [← Real.rpow_one (e + s)]
    rw [← Real.rpow_add hes]
    norm_num
  have hp' : (e + s) ^ (3 / 8 : ℝ) ≤ s ^ (-5 / 8 : ℝ) * (t + e) := by
    rw [hp]
    calc
      _ ≤ (e + s) * s ^ (-5 / 8 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hs (by linarith) (by norm_num)) hes.le
      _ ≤ _ := by
        have : 0 ≤ s ^ (-5 / 8 : ℝ) := by positivity
        nlinarith
  have hb : B ≤ (B / s) * (t + e) := by
    have : B / s * s = B := div_mul_cancel₀ B hs.ne'
    have : 0 ≤ B / s := div_nonneg hB hs.le
    nlinarith [div_mul_cancel₀ B hs.ne']
  have hc : C * e ≤ C * (t + e) := by nlinarith [hs.trans_le hst]
  dsimp [edgeError]
  nlinarith [mul_le_mul_of_nonneg_left hp' hA]

open Set MeasureTheory Filter

lemma third_power_square {x : ℝ} (hx : 0 ≤ x) : (x^(1/3:ℝ))^2 = x^(2/3:ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

lemma fifth_third_power {x : ℝ} (hx : 0 < x) : x^(5/3:ℝ) = x*x^(2/3:ℝ) := by
  rw [show (5/3:ℝ) = 1+2/3 by ring,Real.rpow_add hx,Real.rpow_one]

open Set Filter MeasureTheory

lemma rpow_ratio_tendsto_zero {a ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n:ℝ)^(a-ε)/(n:ℝ)^a) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [Function.comp_def]
  rw [← Real.rpow_sub (Nat.cast_pos.mpr hn)]
  congr 1
  ring

lemma ceil_rpow_ratio_tendsto_zero {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (⌈(n:ℝ)^(a-ε)⌉₊:ℝ)/(n:ℝ)^a) atTop (𝓝 0) := by
  have he := (rpow_ratio_tendsto_zero (a := a) hε).add
    (((tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop))
  rw [zero_add] at he
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) _ he
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ (n:ℝ)^(a-ε) by positivity)).le
  have hp : 0 < (n:ℝ)^a := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) a
  calc
    _ ≤ ((n:ℝ)^(a-ε)+1)/(n:ℝ)^a := div_le_div_of_nonneg_right hc hp.le
    _ = _ := by simp only [Function.comp_def]; rw [add_div,one_div,Real.rpow_neg (Nat.cast_nonneg n)]

end CriticalSK

end

end OAI

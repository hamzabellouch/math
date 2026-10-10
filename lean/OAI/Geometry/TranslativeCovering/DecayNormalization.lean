import OAI.Geometry.TranslativeCovering.CapCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace DecayNormalization

lemma clipped_compare {x H : ℝ} (hx : 0 ≤ x) (hH : 1 ≤ H) (hxH : x ≤ H) :
    x ≤ 2*H*min x (1/2) := by
  by_cases h : x ≤ 1/2
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith

lemma sqrt_clipped {x y H : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hH : 1 ≤ H) (hxH : x ≤ H) (hyH : y ≤ H) :
    Real.sqrt (x*y) ≤ 2*H*Real.sqrt (min x (1/2)*min y (1/2)) := by
  have hbx := lt_min hx (by norm_num : (0:ℝ)<1/2)
  have hby := lt_min hy (by norm_num : (0:ℝ)<1/2)
  have hp := mul_le_mul (clipped_compare hx.le hH hxH) (clipped_compare hy.le hH hyH)
    hy.le (by positivity)
  have hs := Real.sqrt_le_sqrt hp
  have he : (2*H*min x (1/2))*(2*H*min y (1/2)) =
      (2*H)^2*(min x (1/2)*min y (1/2)) := by ring
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by linarith)] at hs
  exact hs

lemma min_ratio {z q s : ℝ} (hzq : z ≤ Real.exp (-q)) (hzs : z ≤ Real.exp (-s)) :
    z / Real.sqrt (Real.exp (-q)*Real.exp (-s)) ≤ Real.exp (-|q-s|/2) := by
  rw [← Real.exp_add, ← Real.exp_half,div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
  rcases le_total q s with hqs | hsq
  · rw [abs_of_nonpos (sub_nonpos.mpr hqs)]
    convert hzs using 1
    congr 1
    ring_nf
  · rw [abs_of_nonneg (sub_nonneg.mpr hsq)]
    convert hzq using 1
    congr 1
    ring_nf

lemma clipped_trivial {z x y H : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hH : 1 ≤ H) (hxH : x ≤ H) (hyH : y ≤ H) (hzx : z ≤ x) (hzy : z ≤ y) :
    z / Real.sqrt (min x (1/2)*min y (1/2)) ≤
      2*H*Real.exp (-|(-Real.log (min x (1/2)))-(-Real.log (min y (1/2)))|/2) := by
  have hHp : 0 < 2*H := by linarith
  have hbx := lt_min hx (by norm_num : (0:ℝ)<1/2)
  have hby := lt_min hy (by norm_num : (0:ℝ)<1/2)
  have hzx' : z/(2*H) ≤ min x (1/2) := (div_le_iff₀ hHp).mpr (by
    nlinarith [hzx.trans (clipped_compare hx.le hH hxH)])
  have hzy' : z/(2*H) ≤ min y (1/2) := (div_le_iff₀ hHp).mpr (by
    nlinarith [hzy.trans (clipped_compare hy.le hH hyH)])
  have heq : Real.exp (-(-Real.log (min x (1/2)))) = min x (1/2) := by rw [neg_neg,Real.exp_log hbx]
  have heq' : Real.exp (-(-Real.log (min y (1/2)))) = min y (1/2) := by rw [neg_neg,Real.exp_log hby]
  have hh := min_ratio (z := z/(2*H)) (q := -Real.log (min x (1/2))) (s := -Real.log (min y (1/2)))
    (by simpa only [heq] using hzx') (by simpa only [heq'] using hzy')
  simp only [heq,heq'] at hh
  rw [div_div, mul_comm (2*H), ← div_div, div_le_iff₀ hHp] at hh
  nlinarith

lemma combine {w C a c X Y D : ℝ}
    (hw : 0 ≤ w) (hC : 0 ≤ C) (_ha : 0 ≤ a) (hc : 0 ≤ c)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hD : D^2 ≤ 2*X+2*Y)
    (hca : c ≤ a/4) (hcy : c ≤ 1/8)
    (h1 : w ≤ C*Real.exp (-a*X)) (h2 : w ≤ C*Real.exp (-Y/2)) :
    w ≤ C*Real.exp (-c*D^2) := by
  have hp := mul_le_mul h1 h2 hw (mul_nonneg hC (Real.exp_pos _).le)
  have he : (C*Real.exp (-a*X))*(C*Real.exp (-Y/2)) =
      C^2*Real.exp (-a*X-Y/2) := by rw [show -a*X-Y/2 = -a*X+(-Y/2) by ring,Real.exp_add]; ring
  rw [he] at hp
  have hexp : -a*X-Y/2 ≤ -2*c*D^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hD hc,
      mul_le_mul_of_nonneg_right hca hX,mul_le_mul_of_nonneg_right hcy hY]
  have hsq : (C*Real.exp (-c*D^2))^2 = C^2*Real.exp (-2*c*D^2) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    norm_num
    ring
  have hnon : 0 ≤ C*Real.exp (-c*D^2) := mul_nonneg hC (Real.exp_pos _).le
  have hcomp := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sq_nonneg C)
  rw [← hsq] at hcomp
  nlinarith

end DecayNormalization

end OAI

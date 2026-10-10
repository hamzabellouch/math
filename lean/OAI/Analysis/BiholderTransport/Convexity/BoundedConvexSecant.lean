import Mathlib

namespace OAI

section
section
noncomputable section
open Set

namespace WeakMTWTransport

lemma bounded_convex_secant {f : ℝ → ℝ} {a b C d x y : ℝ}
    (hf : ConvexOn ℝ (Icc a b) f) (hC : 0 ≤ C) (hd : 0<d)
    (hb : ∀ t∈Icc a b, |f t| ≤ C)
    (hx : x∈Icc (a+d) (b-d)) (hy : y∈Icc (a+d) (b-d)) :
    |f y-f x| ≤ (2*C/d)*|y-x| := by
  wlog hxy : x ≤ y generalizing x y
  · have H := this hy hx (le_of_not_ge hxy)
    simpa only [abs_sub_comm] using H
  obtain rfl | hxy := hxy.eq_or_lt
  · simp
  have hax : a<x := by linarith [hx.1]
  have hyb : y<b := by linarith [hy.2]
  have hxab : x∈Icc a b := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hyab : y∈Icc a b := ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hab : a ≤ b := by linarith
  have haab : a∈Icc a b := ⟨le_rfl,hab⟩
  have hbab : b∈Icc a b := ⟨hab,le_rfl⟩
  have hfa := abs_le.mp (hb a haab)
  have hfb := abs_le.mp (hb b hbab)
  have hfx := abs_le.mp (hb x hxab)
  have hfy := abs_le.mp (hb y hyab)
  have Hlo := hf.slope_mono_adjacent haab hyab hax hxy
  have Hup := hf.slope_mono_adjacent hxab hbab hxy hyb
  have hlo : -(2*C/d) ≤ (f x-f a)/(x-a) := by
    rw [←neg_div,div_le_div_iff₀ hd (sub_pos.mpr hax)]
    have H := mul_le_mul_of_nonneg_right (show -2*C ≤ f x-f a by linarith) hd.le
    have H2 := mul_le_mul_of_nonneg_left (show d ≤ x-a by linarith [hx.1]) (by positivity : 0 ≤ 2*C)
    nlinarith only [H,H2]
  have hup : (f b-f y)/(b-y) ≤ 2*C/d := by
    rw [div_le_div_iff₀ (sub_pos.mpr hyb) hd]
    have H := mul_le_mul_of_nonneg_right (show f b-f y ≤ 2*C by linarith) hd.le
    have H2 := mul_le_mul_of_nonneg_left (show d ≤ b-y by linarith [hy.2]) (by positivity : 0 ≤ 2*C)
    nlinarith only [H,H2]
  have H1 := hlo.trans Hlo
  have H2 := Hup.trans hup
  rw [le_div_iff₀ (sub_pos.mpr hxy)] at H1
  rw [div_le_iff₀ (sub_pos.mpr hxy)] at H2
  rw [abs_of_pos (sub_pos.mpr hxy)]
  exact abs_le.mpr ⟨by nlinarith only [H1],H2⟩

end WeakMTWTransport

end

end

end

end OAI

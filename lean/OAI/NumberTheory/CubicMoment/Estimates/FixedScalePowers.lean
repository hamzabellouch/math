import OAI.NumberTheory.CubicMoment.Estimates.DilatedMomentPowers

namespace OAI

/-! Fixed dilations preserve every strict exponent margin used by the
finite output partition. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventually_const_mul_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ Y : ℝ in atTop, C*Y^a ≤ Y^b := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C] with Y hY hC
  calc
    _ ≤ Y^(b-a)*Y^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hY.le _)
    _ = _ := by rw [← Real.rpow_add hY]; congr 1; ring

lemma eventually_rpow_le_const_mul {a b C : ℝ} (hab : a < b) (hC : 0 < C) :
    ∀ᶠ Y : ℝ in atTop, Y^a ≤ C*Y^b := by
  filter_upwards [eventually_const_mul_rpow_le hab C⁻¹] with Y hY
  calc
    _ = C*(C⁻¹*Y^a) := by rw [← mul_assoc,mul_inv_cancel₀ hC.ne',one_mul]
    _ ≤ C*Y^b := mul_le_mul_of_nonneg_left hY hC.le

lemma eventually_scaled_rpow_le {a b σ : ℝ} (hab : a < b) (hσ : 0 < σ) :
    ∀ᶠ Y : ℝ in atTop, (σ*Y)^a ≤ Y^b := by
  filter_upwards [eventually_ge_atTop (0:ℝ),eventually_const_mul_rpow_le hab (σ^a)] with Y hY h
  rwa [Real.mul_rpow hσ.le hY]

lemma eventually_rpow_le_scaled {a b σ : ℝ} (hab : a < b) (hσ : 0 < σ) :
    ∀ᶠ Y : ℝ in atTop, Y^a ≤ (σ*Y)^b := by
  filter_upwards [eventually_ge_atTop (0:ℝ),eventually_rpow_le_const_mul hab
    (Real.rpow_pos_of_pos hσ b)] with Y hY h
  rwa [Real.mul_rpow hσ.le hY]

lemma eventually_scaled_power_window (a : ℝ) {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    ∀ᶠ Y : ℝ in atTop,
      (σ*Y)^(a-κ) ≤ Y^(a-κ/2) ∧ Y^(a+κ/2) ≤ (σ*Y)^(a+κ) := by
  exact (eventually_scaled_rpow_le (by linarith : a-κ < a-κ/2) hσ).and
    (eventually_rpow_le_scaled (by linarith : a+κ/2 < a+κ) hσ)

lemma eventually_scaled_coordinate_lower {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    ∀ᶠ Y : ℝ in atTop, (2*(σ*Y))^(c/2) ≤ (2*Y)^c := by
  have h₁ := eventually_scaled_rpow_le (by linarith : c/2 < 3*c/4)
    (mul_pos (by norm_num : (0:ℝ) < 2) hσ)
  have h₂ := eventually_rpow_le_scaled (by linarith : 3*c/4 < c) (by norm_num : (0:ℝ) < 2)
  filter_upwards [h₁,h₂] with Y h₁ h₂
  have h₁' : (2*(σ*Y))^(c/2) ≤ Y^(3*c/4) := by simpa only [mul_assoc] using h₁
  exact h₁'.trans h₂

structure FixedScaleMomentBounds (Y σ κ c ε T : ℝ) : Prop where
  threshold : T ≤ σ*Y
  log_bound : 1 ≤ Real.log (σ*Y)
  first_window : (σ*Y)^(1-κ) ≤ Y^(1-κ/2) ∧ Y^(1+κ/2) ≤ (σ*Y)^(1+κ)
  balanced_window : (σ*Y)^(1/3-κ) ≤ Y^(1/3-κ/2) ∧ Y^(1/3+κ/2) ≤ (σ*Y)^(1/3+κ)
  small_bound : Y^(κ/2) ≤ (σ*Y)^κ
  height_bound : Y^(9/25:ℝ) ≤ (σ*Y)^(721/2000:ℝ)
  upper_bound : Y ≤ (σ*Y)^2
  lower_bound : (2*(σ*Y))^(c/2) ≤ (2*Y)^c
  saving_bound : (σ*Y)^(7/3-ε) ≤ Y^(7/3-ε/2)

lemma eventually_fixed_scale_moment_bounds {σ κ c ε : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hc : 0 < c) (hε : 0 < ε) (T : ℝ) :
    ∀ᶠ Y : ℝ in atTop, FixedScaleMomentBounds Y σ κ c ε T := by
  have hlim : Tendsto (fun Y : ℝ => σ*Y) atTop atTop :=
    Tendsto.const_mul_atTop' hσ tendsto_id
  filter_upwards [hlim.eventually_ge_atTop T,
    (Real.tendsto_log_atTop.comp hlim).eventually_ge_atTop 1,
    eventually_scaled_power_window 1 hκ hσ,
    eventually_scaled_power_window (1/3) hκ hσ,
    eventually_rpow_le_scaled (by linarith : κ/2 < κ) hσ,
    eventually_rpow_le_scaled (by norm_num : (9/25:ℝ) < 721/2000) hσ,
    eventually_rpow_le_scaled (by norm_num : (1:ℝ) < 2) hσ,
    eventually_scaled_coordinate_lower hc hσ,
    eventually_scaled_rpow_le (by linarith : 7/3-ε < 7/3-ε/2) hσ]
    with Y hT hlog hfirst hbal hsmall hheight hupper hlower hsave
  refine ⟨hT,hlog,hfirst,hbal,hsmall,hheight,?_,hlower,hsave⟩
  simpa only [Real.rpow_one,Real.rpow_two] using hupper

end CubicFirstMoment

end

end OAI

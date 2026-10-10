import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingLength
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPublishedRate

namespace OAI

/-! A fifth-root logarithmic cap, obtained from the general square-root
cap by substitution. Its size suits the common Diophantine parameter. -/
namespace TwoPointCorrelations

open Filter

noncomputable def majorArcWorkingLength (H : ℕ) (W : ℝ) : ℕ :=
  mrtWorkingLength H (W^(2/5:ℝ))

lemma major_arc_working_root {W : ℝ} (hW : 0 ≤ W) :
    Real.sqrt (W^(2/5:ℝ))=W^(1/5:ℝ) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hW]
  norm_num

lemma major_arc_working_length_le (H : ℕ) (W : ℝ) :
    majorArcWorkingLength H W ≤ H := mrt_working_length_upper

lemma major_arc_working_length_loglog {H : ℕ} {W : ℝ}
    (hW : 0 < W) (hH : (1:ℝ) < majorArcWorkingLength H W) :
    Real.log (Real.log (majorArcWorkingLength H W:ℝ)) ≤ (1/5:ℝ)*Real.log W := by
  have hh := mrt_working_length_loglog (Real.rpow_pos_of_pos hW (2/5)) hH
  rw [Real.log_rpow hW] at hh
  dsimp only [majorArcWorkingLength]
  linarith

lemma major_arc_working_length_exp_upper (H : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (majorArcWorkingLength H W:ℝ) ≤ Real.exp (W^(1/5:ℝ)) := by
  simpa only [majorArcWorkingLength,major_arc_working_root hW] using
    mrt_working_length_exp_upper H (W^(2/5:ℝ))

theorem major_arc_working_length_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) →
      W ≤ Real.log (H:ℝ)^5 → W^a ≤ (majorArcWorkingLength H W:ℝ) := by
  have ht : Tendsto (fun W:ℝ => W^(2/5:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [ht.eventually (mrt_working_cap_power (5*a)),
    mrt_working_original_power a,eventually_ge_atTop (1:ℝ)] with W hcap horiginal hW
  intro H hH hlog hWH
  have hW0 : 0 < W := by linarith
  have hc : W^a ≤ (mrtWorkingCap (W^(2/5:ℝ)):ℝ) := by
    apply le_trans _ hcap
    rw [← Real.rpow_mul_natCast hW0.le (2/5:ℝ) (5*a)]
    rw [show (2/5:ℝ)*(5*a:ℕ)=(2:ℝ)*a by push_cast; ring]
    rw [Real.rpow_mul_natCast hW0.le,Real.rpow_two]
    exact pow_le_pow_left₀ hW0.le (by nlinarith) a
  unfold majorArcWorkingLength mrtWorkingLength
  split_ifs
  · exact horiginal H (by exact_mod_cast hH) hlog hWH
  · exact hc

theorem major_arc_working_length_remainder :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℕ,
      majorArcWorkingLength H W=H ∨
        (majorArcWorkingLength H W:ℝ)/H ≤ W^(-1/4:ℝ) := by
  have ht := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/5 by norm_num)).bound
    (show (0:ℝ)<2 by norm_num)
  filter_upwards [ht,eventually_gt_atTop (0:ℝ)] with W ht hW
  simp only [Real.norm_eq_abs] at ht
  rw [abs_of_nonneg (Real.rpow_nonneg hW.le _)] at ht
  have hlog : Real.log W ≤ 2*W^(1/5:ℝ) := (le_abs_self _).trans ht
  intro H
  unfold majorArcWorkingLength mrtWorkingLength
  rw [major_arc_working_root hW.le]
  split_ifs with h
  · exact Or.inl rfl
  · right
    have hH : Real.exp (W^(1/5:ℝ)) ≤ (H:ℝ) := le_of_not_ge h
    have hH0 : (0:ℝ) < H := (Real.exp_pos _).trans_le hH
    calc
      _ ≤ Real.exp (W^(1/5:ℝ)/2)/(H:ℝ) := by
        apply div_le_div_of_nonneg_right _ hH0.le
        simpa only [major_arc_working_root hW.le] using mrt_working_cap_upper (W^(2/5:ℝ))
      _ ≤ Real.exp (W^(1/5:ℝ)/2)/Real.exp (W^(1/5:ℝ)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hH
      _ = Real.exp (-W^(1/5:ℝ)/2) := by rw [← Real.exp_sub]; congr 1; ring
      _ ≤ _ := by
        rw [Real.rpow_def_of_pos hW (-1/4:ℝ)]
        apply Real.exp_le_exp.mpr
        nlinarith

theorem major_arc_working_cap_log :
    ∀ᶠ W : ℝ in atTop, W^(1/5:ℝ)/4 ≤
      Real.log (mrtWorkingCap (W^(2/5:ℝ)):ℝ) := by
  have ht : Tendsto (fun W:ℝ => W^(2/5:ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [ht.eventually mrt_working_cap_log,eventually_ge_atTop (0:ℝ)] with W hcap hW
  simpa only [major_arc_working_root hW] using hcap

end TwoPointCorrelations

end OAI

import OAI.NumberTheory.TwoPoint.Fourier.MajorArcDivisorBounds
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcRate

namespace OAI

/-! The common major/minor-arc parameter and its quantitative rates.
The fifth-root working length retains the published logarithmic error. -/
namespace TwoPointCorrelations

open Filter

noncomputable def majorArcParameter (L H M : ℝ) : ℝ :=
  min ((Real.log H)^5) (min (L^(1/125:ℝ)) (Real.exp (M/3)))

lemma major_arc_parameter_bounds {L H M : ℝ} (hL : 1 ≤ L)
    (hH : 1 ≤ Real.log H) (hM : 0 ≤ M) :
    1 ≤ majorArcParameter L H M ∧
      majorArcParameter L H M ≤ (Real.log H)^5 ∧
      majorArcParameter L H M ≤ L^(1/125:ℝ) ∧
      majorArcParameter L H M ≤ Real.exp (M/3) := by
  exact ⟨le_min (one_le_pow₀ hH) (le_min
    (Real.one_le_rpow hL (by norm_num)) (Real.one_le_exp (by positivity))),
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

noncomputable def majorArcWorkingError (W : ℝ) : ℝ :=
  (1+Real.log W)*W^(-1/5:ℝ)

lemma major_arc_working_short {H : ℝ} (hH : 1 ≤ Real.log H)
    (hHH : 1 ≤ Real.log (Real.log H)) :
    majorArcWorkingError ((Real.log H)^5) ≤ 6*Real.log (Real.log H)/Real.log H := by
  have hL : 0 < Real.log H := by linarith
  have hp : ((Real.log H)^5)^(-1/5:ℝ) = (Real.log H)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
    norm_num [Real.rpow_neg_one]
  unfold majorArcWorkingError
  rw [hp,Real.log_pow]
  rw [mul_inv_le_iff₀ hL]
  field_simp
  norm_num
  linarith

lemma major_arc_working_exponential {M : ℝ} (hM : 0 ≤ M) :
    majorArcWorkingError (Real.exp (M/3)) ≤ 21*Real.exp (-M/20) := by
  have hh := Real.add_one_le_exp (M/60)
  have hcoef : 1+M/3 ≤ 21*Real.exp (M/60) := by
    have he : 1 ≤ Real.exp (M/60) := Real.one_le_exp (by positivity)
    linarith
  unfold majorArcWorkingError
  rw [Real.log_exp,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  calc
    _ ≤ (21*Real.exp (M/60))*Real.exp (M/3*(-1/5)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring

lemma major_arc_working_outer :
    ∀ᶠ L : ℝ in atTop,
      majorArcWorkingError (L^(1/125:ℝ)) ≤ L^(-1/700:ℝ) := by
  have hh := (isLittleO_log_rpow_atTop (show (0:ℝ)<3/17500 by norm_num)).bound
    (show (0:ℝ)<1/2 by norm_num)
  have hg := (tendsto_rpow_atTop (show (0:ℝ)<3/17500 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hh,hg,eventually_ge_atTop (1:ℝ)] with L hh hg hL
  have hL0 : 0 < L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hh
  have hp : (L^(1/125:ℝ))^(-1/5:ℝ)=L^(-1/625:ℝ) := by
    rw [← Real.rpow_mul hL0.le]
    norm_num
  unfold majorArcWorkingError
  rw [Real.log_rpow hL0,hp]
  calc
    _ ≤ L^(3/17500:ℝ)*L^(-1/625:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL0.le _)
      nlinarith [Real.log_nonneg hL]
    _ = _ := by rw [← Real.rpow_add hL0]; norm_num

lemma major_arc_working_min {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    majorArcWorkingError (min a b) ≤ majorArcWorkingError a+majorArcWorkingError b := by
  have hfa : 0 ≤ majorArcWorkingError a :=
    mul_nonneg (by linarith [Real.log_nonneg ha]) (Real.rpow_nonneg (by linarith) _)
  have hfb : 0 ≤ majorArcWorkingError b :=
    mul_nonneg (by linarith [Real.log_nonneg hb]) (Real.rpow_nonneg (by linarith) _)
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact le_add_of_nonneg_right hfb
  · rw [min_eq_right hba]
    exact le_add_of_nonneg_left hfa

lemma major_arc_parameter_rate :
    ∀ᶠ L : ℝ in atTop, ∀ H M : ℝ, 1 ≤ Real.log H →
      1 ≤ Real.log (Real.log H) → 0 ≤ M →
      majorArcWorkingError (majorArcParameter L H M) ≤
        6*Real.log (Real.log H)/Real.log H + L^(-1/700:ℝ)+21*Real.exp (-M/20) := by
  filter_upwards [major_arc_working_outer,eventually_ge_atTop (1:ℝ)] with L houter hL
  intro H M hH hHH hM
  have ha : 1 ≤ (Real.log H)^5 := one_le_pow₀ hH
  have hb : 1 ≤ L^(1/125:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hc : 1 ≤ Real.exp (M/3) := Real.one_le_exp (by positivity)
  have hi := major_arc_working_min hb hc
  have hj := major_arc_working_min ha (le_min hb hc)
  change majorArcWorkingError (majorArcParameter L H M) ≤ _ at hj
  linarith [major_arc_working_short hH hHH,major_arc_working_exponential hM]

theorem major_arc_sharp_energy_rate :
    ∀ᶠ L : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ L^(1/125:ℝ) →
      Real.sqrt W*(1+Real.log W)*Real.sqrt (Real.log L/L^(1/80:ℝ)) ≤
        101*L^(-1/700:ℝ) := by
  have hs := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/1000 by norm_num)).bound
    (show (0:ℝ)<1 by norm_num)
  filter_upwards [hs,eventually_ge_atTop (1:ℝ)] with L hs hL
  have hL0 : 0 < L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _),one_mul] at hs
  intro W hW hWL
  have hW0 : 0 < W := by linarith
  have hmod : Real.sqrt W*W^(1/100:ℝ) ≤ L^(51/12500:ℝ) := by
    rw [mrt_sqrt_modulus_power hW0]
    calc
      _ ≤ (L^(1/125:ℝ))^(51/100:ℝ) := Real.rpow_le_rpow hW0.le hWL (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hL0.le]; norm_num
  have hratio : Real.log L/L^(1/80:ℝ) ≤ L^(-23/2000:ℝ) := by
    calc
      _ ≤ L^(1/1000:ℝ)/L^(1/80:ℝ) := div_le_div_of_nonneg_right hs (by positivity)
      _ = _ := by rw [← Real.rpow_sub hL0]; norm_num
  have hroot : Real.sqrt (Real.log L/L^(1/80:ℝ)) ≤ L^(-23/4000:ℝ) := by
    calc
      _ ≤ Real.sqrt (L^(-23/2000:ℝ)) := Real.sqrt_le_sqrt hratio
      _ = _ := by rw [Real.sqrt_eq_rpow,← Real.rpow_mul hL0.le]; norm_num
  calc
    _ ≤ Real.sqrt W*(101*W^(1/100:ℝ))*Real.sqrt (Real.log L/L^(1/80:ℝ)) := by
      gcongr
      exact major_arc_log_overhead hW
    _ = 101*((Real.sqrt W*W^(1/100:ℝ))*Real.sqrt (Real.log L/L^(1/80:ℝ))) := by ring
    _ ≤ 101*(L^(51/12500:ℝ)*L^(-23/4000:ℝ)) := by
      gcongr
    _ = 101*L^(-167/100000:ℝ) := by rw [← Real.rpow_add hL0]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)) (by norm_num)

lemma major_arc_sharp_distance_rate {W M : ℝ} (hW : 1 ≤ W) (hM : 0 ≤ M)
    (hWM : W ≤ Real.exp (M/3)) :
    Real.sqrt W*(1+Real.log W)*Real.exp (-2*M/5) ≤ 101*Real.exp (-M/20) := by
  have hW0 : 0 < W := by linarith
  calc
    _ ≤ Real.sqrt W*(101*W^(1/100:ℝ))*Real.exp (-2*M/5) := by
      gcongr
      exact major_arc_log_overhead hW
    _ = 101*(W^(51/100:ℝ)*Real.exp (-2*M/5)) := by
      rw [← mrt_sqrt_modulus_power hW0]
      ring
    _ ≤ 101*((Real.exp (M/3))^(51/100:ℝ)*Real.exp (-2*M/5)) := by
      gcongr
    _ = 101*Real.exp (-23*M/100) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hM])) (by norm_num)


lemma major_arc_inverse_working_rate {W : ℝ} (hW : 1 ≤ W) :
    Real.sqrt W*(1+Real.log W)*W⁻¹ ≤ majorArcWorkingError W := by
  have hW0 : 0 < W := by linarith
  calc
    _ = (1+Real.log W)*W^(-1/2:ℝ) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_neg_one W]
      calc
        _ = (1+Real.log W)*(W^(1/2:ℝ)*W^(-1:ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hW0]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hW (by norm_num))
      (by linarith [Real.log_nonneg hW])

theorem major_arc_weighted_energy_rate :
    ∀ᶠ L : ℝ in atTop, ∀ W M : ℝ, 1 ≤ W → W ≤ L^(1/125:ℝ) →
      0 ≤ M → W ≤ Real.exp (M/3) →
      Real.sqrt W*(1+Real.log W)*
        (Real.exp (-2*M/5)+Real.sqrt (Real.log L/L^(1/80:ℝ))+W⁻¹) ≤
      101*Real.exp (-M/20)+101*L^(-1/700:ℝ)+majorArcWorkingError W := by
  filter_upwards [major_arc_sharp_energy_rate] with L henergy
  intro W M hW hWL hM hWM
  have hm := major_arc_sharp_distance_rate hW hM hWM
  have he := henergy W hW hWL
  have hi := major_arc_inverse_working_rate hW
  calc
    _ = Real.sqrt W*(1+Real.log W)*Real.exp (-2*M/5)+
        Real.sqrt W*(1+Real.log W)*Real.sqrt (Real.log L/L^(1/80:ℝ))+
        Real.sqrt W*(1+Real.log W)*W⁻¹ := by ring
    _ ≤ _ := add_le_add (add_le_add hm he) hi

end TwoPointCorrelations

end OAI

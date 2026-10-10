import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The exact oscillatory kernel of the height-averaged variance. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def heightPhase (v t : ℝ) : ℂ := Complex.exp ((v:ℂ)*Complex.I*(t:ℂ))

def mellinHeightKernel (T v : ℝ) : ℂ :=
  (T:ℂ)⁻¹ * ∫ t in T..2*T, heightPhase v t

@[simp] lemma norm_heightPhase (v t : ℝ) : ‖heightPhase v t‖ = 1 := by
  simp [heightPhase,Complex.norm_exp]

lemma heightPhase_intervalIntegrable (v a b : ℝ) :
    IntervalIntegrable (heightPhase v) volume a b := by
  apply Continuous.intervalIntegrable
  unfold heightPhase
  fun_prop

@[simp] lemma mellinHeightKernel_zero {T : ℝ} (hT : T ≠ 0) :
    mellinHeightKernel T 0 = 1 := by
  simp only [mellinHeightKernel,heightPhase,Complex.ofReal_zero,zero_mul,Complex.exp_zero,
    intervalIntegral.integral_const]
  rw [show 2*T-T = T by ring,Complex.real_smul,mul_one]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hT)


lemma norm_mellinHeightKernel_le_one {T : ℝ} (hT : 0 < T) (v : ℝ) :
    ‖mellinHeightKernel T v‖ ≤ 1 := by
  have hb : ‖∫ t in T..2*T, heightPhase v t‖ ≤ T := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := T) (b := 2*T) (C := (1:ℝ)) (f := heightPhase v)
      (fun t _ => (norm_heightPhase v t).le)
    simpa only [show 2*T-T = T by ring,abs_of_pos hT,one_mul] using h
  rw [mellinHeightKernel,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hT.le)).trans_eq (inv_mul_cancel₀ hT.ne')

lemma mellinHeightKernel_formula (T : ℝ) {v : ℝ} (hv : v ≠ 0) :
    mellinHeightKernel T v = (T:ℂ)⁻¹*
      ((heightPhase v (2*T)-heightPhase v T)/((v:ℂ)*Complex.I)) := by
  unfold mellinHeightKernel heightPhase
  rw [integral_exp_mul_complex (mul_ne_zero (Complex.ofReal_ne_zero.mpr hv) Complex.I_ne_zero)]

lemma norm_mellinHeightKernel_decay {T v : ℝ} (hT : 0 < T) (hv : v ≠ 0) :
    ‖mellinHeightKernel T v‖ ≤ 2/(T*|v|) := by
  have hb : ‖heightPhase v (2*T)-heightPhase v T‖ ≤ 2 := by
    simpa only [norm_heightPhase,one_add_one_eq_two] using norm_sub_le (heightPhase v (2*T)) (heightPhase v T)
  rw [mellinHeightKernel_formula T hv,norm_mul,norm_inv,norm_div,norm_mul,
    Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT,
    Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ T⁻¹*(2/|v|) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hb (abs_nonneg v)) (inv_nonneg.mpr hT.le)
    _ = _ := by ring

lemma normTwist_height_correlation (u t : ℝ) (a b : Eisenstein) :
    normTwist (u+t) a*star (normTwist (u+t) b) =
      (normTwist u a*star (normTwist u b))*heightPhase (Real.log (norm a)-Real.log (norm b)) t := by
  unfold normTwist heightPhase
  change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) =
    (Complex.exp _ * (starRingEnd ℂ) (Complex.exp _))*Complex.exp _
  rw [←Complex.exp_conj,←Complex.exp_conj]
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,←Complex.exp_add]
  congr 1
  push_cast
  ring


lemma averaged_normTwist_correlation (u T : ℝ) (a b : Eisenstein) :
    (T:ℂ)⁻¹*(∫ t in T..2*T, normTwist (u+t) a*star (normTwist (u+t) b)) =
      (normTwist u a*star (normTwist u b))*
        mellinHeightKernel T (Real.log (norm a)-Real.log (norm b)) := by
  simp_rw [normTwist_height_correlation]
  rw [intervalIntegral.integral_const_mul]
  unfold mellinHeightKernel
  ring

end CubicFirstMoment

end

end OAI

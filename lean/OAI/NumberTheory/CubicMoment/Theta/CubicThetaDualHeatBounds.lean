import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLaplaceSum
import OAI.NumberTheory.CubicMoment.Estimates.ThetaHeatKernelBound

namespace OAI

/-! Summable inverse-square majorants for the nonzero Fourier heat modes. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicTheta_inverse_heat_bound {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    Real.exp (-A/t) ≤ (2/A^2)*t^2 := by
  have h := power_exp_bound (by norm_num : (0:ℝ) < 1) 2 (A/t) (div_pos hA ht).le
  norm_num only [one_pow, div_one, Nat.factorial_two, Nat.cast_ofNat, one_mul] at h
  simp only [neg_one_mul] at h
  rw [show (2/A^2)*t^2 = (2*t^2)/A^2 by ring]
  apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
  have hh := (div_le_iff₀ (sq_pos_of_pos ht)).mp
    (show A^2*Real.exp (-A/t)/t^2 ≤ 2 by
      simpa only [div_pow, div_mul_eq_mul_div, neg_div] using h)
  convert hh using 1
  ring

def cubicThetaDualHeat (v : ℝ) (s : ℂ) (A t : ℝ) : ℂ :=
  (t:ℂ)^(s-2)*(Real.exp (-v^2*t-A/t):ℂ)

lemma cubicThetaDualHeat_norm (v : ℝ) (s : ℂ) (A : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖cubicThetaDualHeat v s A t‖ =
      t^(s.re-2)*Real.exp (-v^2*t)*Real.exp (-A/t) := by
  unfold cubicThetaDualHeat
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _), show -v^2*t-A/t = -v^2*t+(-A/t) by ring,
    Real.exp_add]
  simp only [Complex.sub_re, Complex.re_ofNat, mul_assoc]

lemma cubicThetaDualHeat_integrable {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) {A : ℝ} (hA : 0 ≤ A) :
    IntegrableOn (cubicThetaDualHeat v s A) (Ioi 0) := by
  have hm : AEStronglyMeasurable (cubicThetaDualHeat v s A) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaDualHeat
    fun_prop
  have hi := integrable_laplace_rpow (show 0 < s.re-1 by linarith) (sq_pos_of_pos hv)
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [cubicThetaDualHeat_norm v s A ht]
  have he : Real.exp (-A/t) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hA) ht.le)
  calc
    _ ≤ t^(s.re-2)*Real.exp (-v^2*t)*1 :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
    _ = _ := by rw [mul_one, show s.re-1-1 = s.re-2 by ring]

lemma cubicThetaDualHeat_norm_mass_bound {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) {A : ℝ} (hA : 0 < A) :
    (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s A t‖) ≤
      (2/A^2)*(Real.Gamma (s.re+1)*(v^2)^(-(s.re+1))) := by
  have hplus : 0 < s.re+1 := by linarith
  have hi := (integrable_laplace_rpow hplus (sq_pos_of_pos hv)).const_mul (2/A^2)
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), (2/A^2)*(t^((s.re+1)-1)*Real.exp (-v^2*t)) := by
      apply integral_mono_ae (cubicThetaDualHeat_integrable hv hs hA.le).norm hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [cubicThetaDualHeat_norm v s A ht]
      calc
        _ ≤ t^(s.re-2)*Real.exp (-v^2*t)*((2/A^2)*t^2) := by
          exact mul_le_mul_of_nonneg_left (cubicTheta_inverse_heat_bound hA ht)
            (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        _ = _ := by
          have he : t^(s.re-2)*t^2 = t^s.re := by
            rw [← Real.rpow_two, ← Real.rpow_add ht]
            congr 1
            ring
          rw [show (s.re+1)-1 = s.re by ring]
          calc
            _ = (2/A^2)*(t^(s.re-2)*t^2)*Real.exp (-v^2*t) := by ring
            _ = _ := by rw [he]; ring
    _ = _ := by rw [integral_const_mul, laplace_rpow hplus (sq_pos_of_pos hv)]

end CubicFirstMoment

end

end OAI

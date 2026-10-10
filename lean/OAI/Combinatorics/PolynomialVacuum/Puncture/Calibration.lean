import OAI.Combinatorics.PolynomialVacuum.Puncture.MomentWeight
import OAI.Combinatorics.PolynomialVacuum.Puncture.ThermalIntegral

namespace OAI

namespace PolynomialVacuumCylinder
open Real MeasureTheory Set

 
theorem correction_thermal_identity {u : ℝ} (hu : 0<u) :
    Real.log (1+1/(2*Real.cosh u)) =
      thermalLog 1 u-thermalLog 3 u-thermalLog 2 u+thermalLog 4 u := by
  let q := Real.exp (-u)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)
  have hqk (k : ℕ) (hk : 0<k) : 0<1-q^k :=
    sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (Nat.ne_of_gt hk))
  have hc : 0<1+1/(2*Real.cosh u) := by positivity
  have hrel : (1+1/(2*Real.cosh u))*(1-q)*(1-q^4)=(1-q^3)*(1-q^2) := by
    dsimp [q]
    rw [Real.cosh_eq,Real.exp_neg]
    have he : Real.exp u≠0 := (Real.exp_pos u).ne'
    field_simp
    ring
  have hlog := congrArg Real.log hrel
  have hm1 : 0<1-q := sub_pos.mpr hq1
  rw [Real.log_mul (mul_ne_zero hc.ne' hm1.ne') (hqk 4 (by norm_num)).ne',
    Real.log_mul hc.ne' hm1.ne',
    Real.log_mul (hqk 3 (by norm_num)).ne' (hqk 2 (by norm_num)).ne'] at hlog
  have he (k : ℕ) : Real.exp (-(k : ℝ)*u)=q^k := by
    dsimp [q]
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  unfold thermalLog
  have he3 : Real.exp (-3*u)=q^3 := by simpa using he 3
  have he2 : Real.exp (-2*u)=q^2 := by simpa using he 2
  have he4 : Real.exp (-4*u)=q^4 := by simpa using he 4
  rw [he3,he2,he4]
  norm_num only [neg_mul,one_mul]
  dsimp [q] at hlog ⊢
  linarith

theorem correction_scaled_identity {a x : ℝ} (ha : 0<a) (hx : 0<x) :
    Real.log (1+1/(2*Real.cosh (a*x))) =
      thermalLog a x-thermalLog (3*a) x-thermalLog (2*a) x+thermalLog (4*a) x := by
  rw [correction_thermal_identity (mul_pos ha hx)]
  simp only [thermalLog_scale,one_mul]

theorem denominatorCorrection_integral_positive :
    (∫ p : ℝ in Ioi 0,denominatorCorrection p)=5*Real.pi/18 := by
  have ha : 0<Real.pi/4 := by positivity
  have h1 := thermalLog_integrable ha
  have h3 := thermalLog_integrable (mul_pos (by norm_num : (0 : ℝ)<3) ha)
  have h2 := thermalLog_integrable (mul_pos (by norm_num : (0 : ℝ)<2) ha)
  have h4 := thermalLog_integrable (mul_pos (by norm_num : (0 : ℝ)<4) ha)
  have hf : (∫ p : ℝ in Ioi 0,denominatorCorrection p)=
      ∫ p : ℝ in Ioi 0,thermalLog (Real.pi/4) p-thermalLog (3*(Real.pi/4)) p-
        thermalLog (2*(Real.pi/4)) p+thermalLog (4*(Real.pi/4)) p := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro p hp
    convert correction_scaled_identity ha hp using 1
    unfold denominatorCorrection
    congr 4
    ring_nf
  have hi1 := integral_add ((h1.sub h3).sub h2) h4
  have hi2 := integral_sub (h1.sub h3) h2
  have hi3 := integral_sub h1 h3
  simp only [Pi.sub_apply] at hi1 hi2 hi3
  rw [hf,hi1,hi2,hi3,thermalLog_integral ha,
    thermalLog_integral (mul_pos (by norm_num) ha),
    thermalLog_integral (mul_pos (by norm_num) ha),
    thermalLog_integral (mul_pos (by norm_num) ha)]
  field_simp
  ring

 

theorem denominatorCorrection_integral :
    (∫ p : ℝ,denominatorCorrection p)=5*Real.pi/9 := by
  calc
    _ = ∫ p : ℝ,denominatorCorrection |p| := by
      apply integral_congr_ae
      filter_upwards [] with p
      rcases le_total 0 p with hp|hp
      · rw [abs_of_nonneg hp]
      · rw [abs_of_nonpos hp,denominatorCorrection_even]
    _ = 2*∫ p : ℝ in Ioi 0,denominatorCorrection p := integral_comp_abs
    _ = _ := by rw [denominatorCorrection_integral_positive]; ring

theorem denominatorCorrection_integrable : Integrable denominatorCorrection := by
  apply Integrable.of_integral_ne_zero
  rw [denominatorCorrection_integral]
  exact (div_pos (mul_pos (by norm_num) Real.pi_pos) (by norm_num)).ne'

 

theorem denominatorTraceCalibration :
    ((3/8 : ℝ)/(2*Real.pi))*(∫ p : ℝ,denominatorCorrection p)=5/48 := by
  rw [denominatorCorrection_integral]
  field_simp
  ring

end PolynomialVacuumCylinder

end OAI

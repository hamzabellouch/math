import OAI.MeasureTheory.Falconer.Slicing.GaussianEnergy

namespace OAI

/-! # Gaussian smoothing of a bounded frequency-shell measure -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem gaussian_localization_pointwise {B : ℝ} (hB : 1 ≤ B) (u v : Space d)
    (hv : ‖v‖ ≤ 2*B) :
    Real.exp (-2*(dist u v)^2) ≤
      (Real.exp 1*Real.exp (-‖u‖^2/(16*B^2)))*Real.exp (-(dist u v)^2) := by
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  have htri : ‖u‖ ≤ dist u v+‖v‖ := by
    simpa only [dist_zero_right] using dist_triangle u v 0
  have hsq : ‖u‖^2 ≤ 2*(dist u v)^2+8*B^2 := by
    have hsum : ‖u‖ ≤ dist u v+2*B := htri.trans (by linarith)
    have ha := sq_nonneg (dist u v-2*B)
    have hb := mul_nonneg (sub_nonneg.mpr hsum) (show 0 ≤ dist u v+2*B+‖u‖ by positivity)
    nlinarith
  have hnum : ‖u‖^2 ≤ (16*B^2)*((dist u v)^2+1) := by
    have hbase : 1 ≤ B^2 := by nlinarith
    have hh := mul_nonneg (show 0 ≤ 16*B^2-2 by linarith) (sq_nonneg (dist u v))
    nlinarith
  have hdiv : ‖u‖^2/(16*B^2) ≤ (dist u v)^2+1 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [hnum])
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [neg_div]
  linarith

theorem gaussian_localized_mass (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    {B A q : ℝ} {k : ℕ} (hB : 1 ≤ B) (hA : 0 ≤ A) (hq : q ≤ k)
    (hsupport : ∀ᵐ v ∂ρ, ‖v‖ ≤ 2*B)
    (hball : ∀ x : Space d, ∀ r : ℝ, 1 ≤ r →
      ρ (ball x r) ≤ ENNReal.ofReal (A*r^q)) (u : Space d) :
    (∫ v, Real.exp (-2*(dist u v)^2) ∂ρ) ≤
      Real.exp 1*A*gaussianBallConstant k*Real.exp (-‖u‖^2/(16*B^2)) := by
  have hint (a : ℝ) (ha : 0 ≤ a) :
      Integrable (fun v => Real.exp (-a*(dist u v)^2)) ρ := by
    apply (integrable_const (1:ℝ)).mono (by fun_prop)
    filter_upwards with v
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _))
  have hpotential : (∫ v, Real.exp (-(dist u v)^2) ∂ρ) ≤ A*gaussianBallConstant k := by
    have h := gaussian_mass_bound_real ρ (B := 1) zero_lt_one hA hq
      (by simpa only [div_one] using hball) u
    simpa using h
  have h1 : Integrable (fun v => Real.exp (-(dist u v)^2)) ρ := by
    simpa only [neg_mul,one_mul] using hint 1 zero_le_one
  calc
    _ ≤ ∫ v, (Real.exp 1*Real.exp (-‖u‖^2/(16*B^2)))*
        Real.exp (-(dist u v)^2) ∂ρ := by
      apply integral_mono_ae (hint 2 (by norm_num))
        (h1.const_mul _)
      filter_upwards [hsupport] with v hv
      exact gaussian_localization_pointwise hB u v hv
    _ = (Real.exp 1*Real.exp (-‖u‖^2/(16*B^2)))*
        (∫ v, Real.exp (-(dist u v)^2) ∂ρ) := integral_const_mul _ _
    _ ≤ (Real.exp 1*Real.exp (-‖u‖^2/(16*B^2)))*(A*gaussianBallConstant k) :=
      mul_le_mul_of_nonneg_left hpotential (by positivity)
    _ = _ := by ring

end Falconer

end OAI

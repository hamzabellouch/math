import OAI.Probability.SLE.Angle.AngleEigenDifferential

namespace OAI

/-! The stationary angular weight puts the cosine generator in divergence
form. Its flux vanishes at both endpoints of the actual angle interval. -/
noncomputable section
open Polynomial Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology

namespace SLEExactGauge

def anglePolynomialFlux (κ : ℝ) (p : ℝ[X]) (θ : ℝ) : ℝ :=
  -(κ/8)*Real.sin θ^(4*Target.a κ+1)*p.derivative.eval (Real.cos θ)

lemma anglePolynomialFlux_hasDerivAt {κ : ℝ} (hκ : 0<κ) (p : ℝ[X]) {θ : ℝ}
    (hθ : θ∈Icc (0:ℝ) Real.pi) :
    HasDerivAt (anglePolynomialFlux κ p)
      (Real.sin θ^(4*Target.a κ)*(anglePolynomialGenerator κ p).eval (Real.cos θ)) θ := by
  have hp : 0<4*Target.a κ := by unfold Target.a; positivity
  have hpow := (Real.hasDerivAt_sin θ).rpow_const
    (Or.inr (by linarith : 1≤4*Target.a κ+1))
  have hpol := (p.derivative.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)
  apply ((hpow.const_mul (-(κ/8))).mul hpol).congr_deriv
  dsimp only [Function.comp_apply]
  have hs : 0≤Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  rw [show 4*Target.a κ+1-1=4*Target.a κ by ring]
  by_cases hz : Real.sin θ=0
  · simp only [hz,Real.zero_rpow hp.ne',Real.zero_rpow (by linarith : 4*Target.a κ+1≠0),
      mul_zero,zero_mul,add_zero]
  · have hsp : 0<Real.sin θ := lt_of_le_of_ne hs (Ne.symm hz)
    rw [Real.rpow_add hsp,Real.rpow_one]
    simp only [anglePolynomialGenerator,eval_sub,eval_mul,eval_C,eval_one,eval_pow,eval_X]
    have hsin : Real.sin θ^2=1-Real.cos θ^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [← hsin]
    unfold Target.a
    field_simp
    ring

lemma anglePolynomialGenerator_stationary_integral {κ : ℝ} (hκ : 0<κ) (p : ℝ[X]) :
    (∫ θ in (0:ℝ)..Real.pi,
      Real.sin θ^(4*Target.a κ)*(anglePolynomialGenerator κ p).eval (Real.cos θ))=0 := by
  have hp : 0<4*Target.a κ := by unfold Target.a; positivity
  have hc : Continuous (fun θ : ℝ =>
      Real.sin θ^(4*Target.a κ)*(anglePolynomialGenerator κ p).eval (Real.cos θ)) :=
    ((Real.continuous_rpow_const hp.le).comp Real.continuous_sin).mul
      ((anglePolynomialGenerator κ p).continuous.comp Real.continuous_cos)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ hθ => anglePolynomialFlux_hasDerivAt hκ p
      (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ)) (hc.intervalIntegrable 0 Real.pi)
  simpa only [anglePolynomialFlux,Real.sin_pi,Real.sin_zero,
    Real.zero_rpow (by linarith : 4*Target.a κ+1≠0),mul_zero,zero_mul,sub_self] using he

end SLEExactGauge

end

end OAI

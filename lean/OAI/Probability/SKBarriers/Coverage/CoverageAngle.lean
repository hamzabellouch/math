import Mathlib

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def coverageAngle (L : ℕ → ℝ) (M : ℝ) (n : ℕ) : ℝ := Real.sqrt (M*L n/(n:ℝ))

theorem coverageAngle_tendsto (L : ℕ → ℝ) (M : ℝ)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (coverageAngle L M) atTop (𝓝 0) := by
  have H := (hsub.const_mul M).sqrt
  change Tendsto (fun n => Real.sqrt (M*L n/(n:ℝ))) atTop (𝓝 0)
  simpa only [← mul_div_assoc,mul_zero,Real.sqrt_zero] using H

theorem coverageAngle_pos {L : ℕ → ℝ} {M : ℝ} (hM : 0 < M) {n : ℕ}
    (hn : 0 < n) (hL : 0 < L n) : 0 < coverageAngle L M n := by
  unfold coverageAngle
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  positivity

theorem sin_eq_sinc_mul (x : ℝ) : Real.sin x = Real.sinc x*x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx,div_mul_cancel₀ _ hx]

theorem coverageAngle_variance_tendsto (L : ℕ → ℝ) {M β : ℝ} (hM : 0 < M)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (β*Real.sin (coverageAngle L M n))^2*(n:ℝ)/L n)
      atTop (𝓝 (β^2*M)) := by
  have hsinc : Tendsto (fun n => Real.sinc (coverageAngle L M n)) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp (coverageAngle_tendsto L M hsub)
  have H := (hsinc.pow 2).const_mul (β^2*M)
  simp only [one_pow,mul_one] at H
  apply H.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (0:ℕ)] with n hLn hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hθ : coverageAngle L M n^2 = M*L n/(n:ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [sin_eq_sinc_mul,mul_pow,mul_pow,hθ]
  field_simp

theorem coverageAngle_loss_tendsto (L : ℕ → ℝ) {M β e : ℝ} (hM : 0 < M)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => β*(Real.cos (coverageAngle L M n)-1)*(n:ℝ)*e/L n)
      atTop (𝓝 (-β*M*e/2)) := by
  have hθ := coverageAngle_tendsto L M hsub
  have hsinc : Tendsto (fun n => Real.sinc (coverageAngle L M n)) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp hθ
  have hcos : Tendsto (fun n => Real.cos (coverageAngle L M n)) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp hθ
  have H := ((hsinc.pow 2).const_mul (-β*M*e)).div (tendsto_const_nhds.add hcos)
    (by norm_num : (1:ℝ)+1 ≠ 0)
  norm_num only [one_pow,mul_one,one_add_one_eq_two] at H
  apply H.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (0:ℕ),
    hcos.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))] with n hLn hn hc
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hθsq : coverageAngle L M n^2 = M*L n/(n:ℝ) := Real.sq_sqrt (by positivity)
  have htrig := Real.sin_sq_add_cos_sq (coverageAngle L M n)
  rw [sin_eq_sinc_mul,mul_pow,hθsq] at htrig
  have hden : 1+Real.cos (coverageAngle L M n) ≠ 0 := by positivity
  have hcosEq : Real.cos (coverageAngle L M n)-1 =
      -(Real.sinc (coverageAngle L M n)^2*(M*L n/(n:ℝ)))/(1+Real.cos (coverageAngle L M n)) := by
    apply (eq_div_iff hden).mpr
    nlinarith
  change -β*M*e*Real.sinc (coverageAngle L M n)^2/(1+Real.cos (coverageAngle L M n)) =
    β*(Real.cos (coverageAngle L M n)-1)*(n:ℝ)*e/L n
  rw [hcosEq]
  field_simp

end SK.Analytic

end
end

end

end OAI

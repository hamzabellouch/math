import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPolynomial
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace OAI

/-! Coefficient bounds for the nonlinear expansion from a fixed small circle. -/

open Polynomial Set Filter
namespace DefocusingNLS

theorem radialPolynomial_coefficient_bound (P : ℂ[X]) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ z : ℂ, ‖z‖=1 → ‖P.eval z‖ ≤ C) (k : ℕ) : ‖P.coeff k‖ ≤ C := by
  have hs : ‖P.coeff k‖^2 ≤ ∑ i ∈ P.support, ‖P.coeff i‖^2 := by
    by_cases hk : k ∈ P.support
    · exact Finset.single_le_sum (fun i _ => sq_nonneg ‖P.coeff i‖) hk
    · simp only [mem_support_iff,not_not] at hk
      simp only [hk,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      positivity
  rw [P.sum_sq_norm_coeff_eq_circleAverage] at hs
  have hi : CircleIntegrable (fun z : ℂ => ‖P.eval z‖^2) 0 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    fun_prop
  have hb := Real.circleAverage_mono_on_of_le_circle hi (a := C^2) (fun z hz => by
    have hz1 : ‖z‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right,abs_one] using hz
    exact pow_le_pow_left₀ (norm_nonneg _) (hP z hz1) 2)
  nlinarith [norm_nonneg (P.coeff k)]

theorem radialPolynomial_coefficient_scaled_bound (P : ℂ[X]) (ε C : ℝ)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hP : ∀ z : ℂ, ‖z‖=ε → ‖P.eval z‖ ≤ C) (k : ℕ) :
    ‖P.coeff k‖*ε^k ≤ C := by
  have hQ : ∀ z : ℂ, ‖z‖=1 → ‖(P.comp (Polynomial.C (ε : ℂ)*X)).eval z‖ ≤ C := by
    intro z hz
    simp only [eval_comp,eval_mul,eval_C,eval_X]
    apply hP
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hε,hz,mul_one]
  have hb := radialPolynomial_coefficient_bound (P.comp (Polynomial.C (ε : ℂ)*X)) C hC hQ k
  simpa only [comp_C_mul_X_coeff,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hε] using hb

theorem radialPolynomialPower_circle_bound (P : ℂ[X]) (n : ℕ) (ε ρ : ℝ)
    (hρ : 0 ≤ ρ) (hP : ∀ z : ℂ, ‖z‖=ε → ‖P.eval z‖ ≤ ρ)
    (z : ℂ) (hz : ‖z‖=ε) : ‖(radialPolynomialPower n P).eval z‖ ≤ ρ^(2*n+1) := by
  have hc : (Polynomial.mapRingHom (starRingEnd ℂ) P).eval z=star (P.eval (star z)) := by
    simpa using (Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) (star z))
  have hp := hP z hz
  have hpc := hP (star z) (by simpa only [norm_star] using hz)
  simp only [radialPolynomialPower,eval_mul,eval_pow,hc,norm_mul,norm_pow,norm_star]
  calc
    _ ≤ ρ^(n+1)*ρ^n := by gcongr
    _ = ρ^(2*n+1) := by rw [← pow_add]; congr 1; omega

theorem radialPolynomialPower_coefficient_bound (P : ℂ[X]) (n k : ℕ) (ε ρ : ℝ)
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hP : ∀ z : ℂ, ‖z‖=ε → ‖P.eval z‖ ≤ ρ) :
    ‖(radialPolynomialPower n P).coeff k‖*ε^k ≤ ρ^(2*n+1) :=
  radialPolynomial_coefficient_scaled_bound _ ε _ hε (pow_nonneg hρ _)
    (radialPolynomialPower_circle_bound P n ε ρ hρ hP) k

theorem radialPolynomialPower_coefficient_tendsto (P : ℕ → ℂ[X]) (k : ℕ) (ε ρ : ℝ)
    (hε : 0 < ε) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP : ∀ᶠ n : ℕ in atTop, ∀ z, ‖z‖=ε → ‖(P n).eval z‖ ≤ ρ) :
    Tendsto (fun n => (radialPolynomialPower n (P n)).coeff k) atTop (nhds 0) := by
  have hq : ρ^2 < 1 := pow_lt_one₀ hρ hρ1 (by decide : 2 ≠ 0)
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ρ) hq).const_mul (ρ/ε^k)
  simp only [mul_zero] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [hP] with n hn
  have hb := radialPolynomialPower_coefficient_bound (P n) n k ε ρ hε.le hρ hn
  have hb' := (le_div_iff₀ (pow_pos hε k)).mpr hb
  calc
    _ ≤ ρ^(2*n+1)/ε^k := hb'
    _ = (ρ/ε^k)*(ρ^2)^n := by rw [pow_add,pow_one,pow_mul]; ring

end DefocusingNLS

end OAI

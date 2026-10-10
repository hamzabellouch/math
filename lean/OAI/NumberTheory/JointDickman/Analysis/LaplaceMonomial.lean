import OAI.NumberTheory.JointDickman.Counting.HankelGammaCoefficients

namespace OAI

/-! # Integrating the monomials in the analytic singular factor -/
namespace JointDickman
open MeasureTheory Set

 theorem laplace_monomial_eq {z L t : ℝ} (ht : 0 < t) (j : ℕ) (a : ℂ) :
    (t^(-z)*Real.exp (-(L*t))) • (a*(t:ℂ)^j) =
      (t^((j:ℝ)-z)*Real.exp (-(L*t))) • a := by
  have he : t^((j:ℝ)-z)*Real.exp (-(L*t)) = (t^(-z)*Real.exp (-(L*t)))*t^j := by
    rw [show (j:ℝ)-z = -z+j by ring,Real.rpow_add ht,Real.rpow_natCast]
    ring
  rw [he]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

 theorem laplace_monomial_integrable {z L : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (j : ℕ) (a : ℂ) {S : Set ℝ} (hSm : MeasurableSet S) (hS : S ⊆ Ioi 0) :
    IntegrableOn (fun t : ℝ => (t^(-z)*Real.exp (-(L*t))) • (a*(t:ℂ)^j)) S := by
  have h := (fractional_laplace_integrable hz1 hL j).smul_const a
  apply (IntegrableOn.mono_set h hS).congr_fun _ hSm
  intro t ht
  exact (laplace_monomial_eq (hS ht) j a).symm

 theorem laplace_monomial_integral {z L : ℝ} (j : ℕ) (a : ℂ) {S : Set ℝ}
    (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0) :
    (∫ t : ℝ in S, (t^(-z)*Real.exp (-(L*t))) • (a*(t:ℂ)^j)) =
      (∫ t : ℝ in S, t^((j:ℝ)-z)*Real.exp (-(L*t))) • a := by
  calc
    _ = ∫ t : ℝ in S, (t^((j:ℝ)-z)*Real.exp (-(L*t))) • a := by
      apply setIntegral_congr_fun hS
      intro t ht
      exact laplace_monomial_eq (hS0 ht) j a
    _ = _ := integral_smul_const _ _

 theorem laplace_monomial_integral_Ioi {z L : ℝ} (hz1 : z < 1) (hL : 0 < L) (j : ℕ) (a : ℂ) :
    (∫ t : ℝ in Ioi 0, (t^(-z)*Real.exp (-(L*t))) • (a*(t:ℂ)^j)) =
      (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • a := by
  rw [laplace_monomial_integral j a measurableSet_Ioi (fun _ h => h),fractional_laplace_gamma hz1 hL j]

end JointDickman

end OAI

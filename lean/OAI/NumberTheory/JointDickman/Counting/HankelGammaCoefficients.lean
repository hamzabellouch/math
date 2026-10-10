import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace OAI

/-! # Laplace moments of the fractional-power jump

For the two squarefree exponents, `0 < z < 1`. The upper/lower boundary
values of a power on the negative real axis give the sine factor below.
Euler reflection turns each Laplace moment into the required reciprocal
Gamma coefficient.
-/
namespace JointDickman
open MeasureTheory Set

 theorem gamma_sub_nat_ne_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (j : ℕ) :
    Real.Gamma (z-j) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m he
  rcases lt_or_ge m j with hmj | hjm
  · have hh : (m:ℝ)+1 ≤ j := by exact_mod_cast hmj
    linarith
  · have hh : (j:ℝ) ≤ m := by exact_mod_cast hjm
    linarith

 theorem gamma_reflection_coefficient {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (j : ℕ) :
    Real.sin (Real.pi*(z-j))/Real.pi * Real.Gamma ((j:ℝ)+1-z) = 1/Real.Gamma (z-j) := by
  have ha := gamma_sub_nat_ne_zero hz hz1 j
  have hb : 0 < Real.Gamma ((j:ℝ)+1-z) := Real.Gamma_pos_of_pos (by have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have hr := Real.Gamma_mul_Gamma_one_sub (z-j)
  rw [show 1-(z-j) = (j:ℝ)+1-z by ring] at hr
  have hs : Real.sin (Real.pi*(z-j)) ≠ 0 := by
    intro he
    rw [he,div_zero] at hr
    exact (mul_ne_zero ha hb.ne') hr
  apply (eq_div_iff ha).mpr
  calc
    _ = (Real.Gamma (z-j)*Real.Gamma ((j:ℝ)+1-z))*Real.sin (Real.pi*(z-j))/Real.pi := by ring
    _ = 1 := by rw [hr]; field_simp

 theorem fractional_laplace_integrable {z L : ℝ} (hz1 : z < 1) (hL : 0 < L) (j : ℕ) :
    IntegrableOn (fun t : ℝ => t^((j:ℝ)-z)*Real.exp (-(L*t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (j:ℝ)-z)
    (by have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith) (by norm_num) hL
  simpa only [Real.rpow_one,neg_mul] using h

 theorem fractional_laplace_gamma {z L : ℝ} (hz1 : z < 1) (hL : 0 < L) (j : ℕ) :
    (∫ t : ℝ in Ioi 0, t^((j:ℝ)-z)*Real.exp (-(L*t))) =
      L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j:ℝ)+1-z)
    (by have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith) hL
  have hp : (1/L)^((j:ℝ)+1-z) = L^(z-j-1) := by
    rw [one_div,Real.inv_rpow hL.le,← Real.rpow_neg hL.le]
    congr 1
    ring
  simpa only [show (j:ℝ)+1-z-1 = j-z by ring,hp] using h

 theorem hankel_gamma_coefficient {z L : ℝ} (hz : 0 < z) (hz1 : z < 1) (hL : 0 < L) (j : ℕ) :
    Real.sin (Real.pi*(z-j))/Real.pi *
      (∫ t : ℝ in Ioi 0, t^((j:ℝ)-z)*Real.exp (-(L*t))) =
      L^(z-j-1)/Real.Gamma (z-j) := by
  rw [fractional_laplace_gamma hz1 hL j]
  calc
    _ = L^(z-j-1)*(Real.sin (Real.pi*(z-j))/Real.pi*Real.Gamma ((j:ℝ)+1-z)) := by ring
    _ = _ := by rw [gamma_reflection_coefficient hz hz1 j]; ring

end JointDickman

end OAI

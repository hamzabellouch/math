import OAI.NumberTheory.JointDickman.Analysis.LaplaceMonomial
import OAI.NumberTheory.JointDickman.Analysis.LaplaceIntegrability
import OAI.NumberTheory.JointDickman.Analysis.LaplaceCutoff
import Mathlib.Analysis.Complex.Asymptotics

namespace OAI

/-! # Finite Taylor polynomials under a truncated Laplace integral -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem laplace_polynomial_integrable {z L η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (a : ℕ → ℂ) (H : ℕ) :
    IntegrableOn (fun t : ℝ => (t^(-z)*Real.exp (-(L*t))) •
      (∑ j ∈ range (H+1), a j*(t:ℂ)^j)) (Ioc 0 η) := by
  have h := integrable_finsetSum (range (H+1)) (fun j _ =>
    laplace_monomial_integrable hz1 hL j (a j) (S := Ioc 0 η) measurableSet_Ioc Ioc_subset_Ioi_self)
  simpa only [IntegrableOn,smul_sum] using h

theorem laplace_polynomial_integral {z L η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (a : ℕ → ℂ) (H : ℕ) :
    (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
      (∑ j ∈ range (H+1), a j*(t:ℂ)^j)) =
      ∑ j ∈ range (H+1), (∫ t : ℝ in Ioc 0 η,
        t^((j:ℝ)-z)*Real.exp (-(L*t))) • a j := by
  simp_rw [smul_sum]
  rw [integral_finsetSum (range (H+1)) (fun j _ =>
    laplace_monomial_integrable hz1 hL j (a j) measurableSet_Ioc Ioc_subset_Ioi_self)]
  exact sum_congr rfl (fun j _ => laplace_monomial_integral j (a j)
    measurableSet_Ioc Ioc_subset_Ioi_self)

theorem laplace_polynomial_cutoff_error {z η : ℝ} (hz1 : z < 1) (hη : 0 < η)
    (a : ℕ → ℂ) (H : ℕ) (b : ℝ) :
    (fun L : ℝ => (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
      (∑ j ∈ range (H+1), a j*(t:ℂ)^j)) -
      ∑ j ∈ range (H+1), (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • a j)
      =o[atTop] (fun L => L^b) := by
  have h (j : ℕ) : (fun L : ℝ => ((∫ t : ℝ in Ioc 0 η,
      t^((j:ℝ)-z)*Real.exp (-(L*t))) -
        L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • a j) =o[atTop] (fun L => L^b) := by
    have hc := (Complex.isLittleO_ofReal_left.mpr
      (fractional_laplace_cutoff_error hz1 hη j b)).const_mul_left (a j)
    simpa only [Complex.real_smul,mul_comm] using hc
  apply (IsLittleO.sum (s := range (H+1)) (fun j _ => h j)).congr' _
    (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [laplace_polynomial_integral hz1 hL a H]
  simp only [Finset.sum_apply,sub_smul,sum_sub_distrib]

end JointDickman

end OAI

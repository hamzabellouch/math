import Mathlib

namespace OAI

namespace PolynomialVacuumCylinder
open Real MeasureTheory Set

 
noncomputable def thermalLog (a x : ℝ) : ℝ := -Real.log (1-Real.exp (-a*x))
noncomputable def thermalTerm (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(a*((k : ℝ)+1))*x)/((k : ℝ)+1)

theorem thermalTerm_integrable {a : ℝ} (ha : 0<a) (k : ℕ) :
    IntegrableOn (thermalTerm a k) (Ioi 0) := by
  exact (exp_neg_integrableOn_Ioi 0 (mul_pos ha (by positivity))).div_const _

theorem thermalTerm_integral {a : ℝ} (ha : 0<a) (k : ℕ) :
    (∫ x : ℝ in Ioi 0, thermalTerm a k x) = (1/a)*(1/((k : ℝ)+1)^2) := by
  unfold thermalTerm
  rw [integral_div,integral_exp_mul_Ioi (neg_neg_of_pos (mul_pos ha (by positivity))) 0]
  simp only [mul_zero,Real.exp_zero]
  field_simp

theorem thermalLog_series {a x : ℝ} (ha : 0<a) (hx : 0<x) :
    HasSum (fun k=>thermalTerm a k x) (thermalLog a x) := by
  have h : |Real.exp (-a*x)|<1 := by
    rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos ha) hx
  have hfun : (fun k : ℕ=>thermalTerm a k x)=
      (fun k : ℕ=>Real.exp (-a*x)^(k+1)/((k : ℝ)+1)) := by
    funext k
    dsimp [thermalTerm]
    rw [←Real.exp_nat_mul]
    push_cast
    congr 1
    congr 1
    ring
  rw [hfun]
  exact Real.hasSum_pow_div_log_of_abs_lt_one h

theorem thermalLog_integral {a : ℝ} (ha : 0<a) :
    (∫ x : ℝ in Ioi 0, thermalLog a x)=Real.pi^2/(6*a) := by
  have hz : HasSum (fun k : ℕ=>1/((k : ℝ)+1)^2) (Real.pi^2/6) := by
    have hz0 : HasSum (fun n : ℕ=>(1 : ℝ)/(n : ℝ)^2)
        (Real.pi^2/6+∑i∈Finset.range 1,(1 : ℝ)/(i : ℝ)^2) := by
      simpa using hasSum_zeta_two
    simpa using (hasSum_nat_add_iff 1).2 hz0
  have hsum : Summable (fun k=>∫ x : ℝ in Ioi 0, ‖thermalTerm a k x‖) := by
    have hfun : (fun k : ℕ=>∫ x : ℝ in Ioi 0, ‖thermalTerm a k x‖)=
        (fun k : ℕ=>(1/a)*(1/((k : ℝ)+1)^2)) := by
      funext k
      rw [show (fun x : ℝ=>‖thermalTerm a k x‖)=thermalTerm a k by
        funext x; exact Real.norm_of_nonneg (by unfold thermalTerm; positivity),
        thermalTerm_integral ha]
    rw [hfun]
    exact (hz.mul_left (1/a)).summable
  have he := integral_tsum_of_summable_integral_norm (fun k=>thermalTerm_integrable ha k) hsum
  have hs : (∑' k,∫ x : ℝ in Ioi 0, thermalTerm a k x)=Real.pi^2/(6*a) := by
    simp_rw [thermalTerm_integral ha]
    rw [(hz.mul_left (1/a)).tsum_eq]
    ring
  rw [hs] at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact (thermalLog_series ha hx).tsum_eq.symm

theorem thermalLog_integrable {a : ℝ} (ha : 0<a) :
    IntegrableOn (thermalLog a) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [thermalLog_integral ha]
  exact (div_pos (sq_pos_of_pos Real.pi_pos) (mul_pos (by norm_num) ha)).ne'

theorem thermalLog_scale (a b x : ℝ) : thermalLog a (b*x)=thermalLog (a*b) x := by
  unfold thermalLog
  congr 3
  ring_nf

end PolynomialVacuumCylinder

end OAI

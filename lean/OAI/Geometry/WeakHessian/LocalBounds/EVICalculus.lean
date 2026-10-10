import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile71
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma exp_integral_average_tendsto {E : ℝ → ℝ} (hE : Continuous E) (K x : ℝ) :
    Tendsto (fun h : ℝ => (∫ s in 0..h,Real.exp (K*s)*E (x+s))/h)
      (𝓝[>] 0) (𝓝 (E x)) := by
  have hc : Continuous (fun s : ℝ => Real.exp (K*s)*E (x+s)) := by fun_prop
  have H := (hc.integral_hasStrictDerivAt 0 0).hasDerivAt.tendsto_slope_zero_right
  simpa only [zero_add,intervalIntegral.integral_same,sub_zero,smul_eq_mul,div_eq_mul_inv,
    mul_zero,Real.exp_zero,one_mul,mul_one,add_zero,mul_comm] using H

lemma exp_entropy_average_identity {E : ℝ → ℝ} (hE : Continuous E) (K x z h : ℝ) :
    (∫ s in 0..h,Real.exp (K*s)*(z-E (x+s)))/h =
      z*((∫ s in 0..h,Real.exp (K*s))/h)-(∫ s in 0..h,Real.exp (K*s)*E (x+s))/h := by
  have hf : (fun s : ℝ => Real.exp (K*s)*(z-E (x+s))) =
      fun s => z*Real.exp (K*s)-Real.exp (K*s)*E (x+s) := by funext s; ring
  rw [hf,intervalIntegral.integral_sub ((by fun_prop : Continuous (fun s : ℝ => Real.exp (K*s))).intervalIntegrable _ _ |>.const_mul z)
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (K*s)*E (x+s))).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  ring

lemma evi_error_ratio_tendsto {E F : ℝ → ℝ} (hE : Continuous E) (hF : Continuous F) (K x : ℝ) :
    Tendsto (fun h : ℝ => 2*Real.exp (2*K*x)*
      (Real.exp (K*h)*((∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))/h)+
        (∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s)))/h)) (𝓝[>] 0) (𝓝 0) := by
  have hA : Tendsto (fun h : ℝ => (∫ s in 0..h,Real.exp (K*s))/h) (𝓝[>] 0) (𝓝 1) := by
    simpa only [mul_one] using exp_integral_average_tendsto (E := fun _ => (1:ℝ)) continuous_const K x
  have hFt : Tendsto (fun h : ℝ => F (x+h)) (𝓝[>] 0) (𝓝 (F x)) := by
    simpa only [add_zero] using ((by fun_prop : Continuous (fun h : ℝ => F (x+h))).tendsto 0).mono_left nhdsWithin_le_nhds
  have hExp : Tendsto (fun h : ℝ => Real.exp (K*h)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [mul_zero,Real.exp_zero] using ((by fun_prop : Continuous (fun h : ℝ => Real.exp (K*h))).tendsto 0).mono_left nhdsWithin_le_nhds
  simp_rw [exp_entropy_average_identity hE,exp_entropy_average_identity hF]
  have H := ((hExp.mul ((hFt.mul hA).sub (exp_integral_average_tendsto hE K x))).add
    ((hA.const_mul (E x)).sub (exp_integral_average_tendsto hF K x))).const_mul (2*Real.exp (2*K*x))
  simpa only [mul_one,one_mul,sub_add_sub_cancel,sub_self,mul_zero] using H

lemma evi_rectangle {D : ℝ → ℝ → ℝ} {E F : ℝ → ℝ} {K x h : ℝ}
    (h1 : (Real.exp (K*h)*D (x+h) (x+h)-D x (x+h))/2 ≤
      ∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))
    (h2 : (Real.exp (K*h)*D x (x+h)-D x x)/2 ≤
      ∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s))) (hh : 0 < h) :
    (Real.exp (2*K*(x+h))*D (x+h) (x+h)-Real.exp (2*K*x)*D x x)/h ≤
      2*Real.exp (2*K*x)*(Real.exp (K*h)*((∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))/h)+
        (∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s)))/h) := by
  have he : Real.exp (2*K*(x+h)) = Real.exp (2*K*x)*(Real.exp (K*h)*Real.exp (K*h)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  rw [he]
  have H := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (K*h)).le
  have H' : (Real.exp (K*h)*Real.exp (K*h))*D (x+h) (x+h)-D x x ≤
      2*(Real.exp (K*h)*(∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))+
        (∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s)))) := by nlinarith
  have H'' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left H' (Real.exp_pos (2*K*x)).le) hh.le
  calc
    _ = Real.exp (2*K*x)*((Real.exp (K*h)*Real.exp (K*h))*D (x+h) (x+h)-D x x)/h := by ring
    _ ≤ Real.exp (2*K*x)*(2*(Real.exp (K*h)*(∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))+
        (∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s)))))/h := H''
    _ = _ := by ring
end WeakHessian

end
end InlinedFile71

end OAI

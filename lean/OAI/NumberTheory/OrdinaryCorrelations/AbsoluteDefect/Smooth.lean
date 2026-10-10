import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinarySharpWindow
open MeasureTheory Finset

noncomputable def smooth (G : ℝ→ℝ) (V : ℝ→ℂ) (x : ℝ) : ℂ :=
  ∫z : ℝ,(G z:ℂ)*V (x-z)

lemma smooth_joint_integrable {G : ℝ→ℝ} {V : ℝ→ℂ}
    (hG : Integrable G) (hV : Integrable V) :
    Integrable (fun p : ℝ×ℝ=>(G p.2:ℂ)*V (p.1-p.2)) (volume.prod volume) := by
  exact hG.ofReal.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hV

lemma smooth_integrable {G : ℝ→ℝ} {V : ℝ→ℂ}
    (hG : Integrable G) (hV : Integrable V) : Integrable (smooth G V) :=
  (smooth_joint_integrable hG hV).integral_prod_left

theorem smooth_error_l1 {G : ℝ→ℝ} {V : ℝ→ℂ} {K : ℝ}
    (hG : Integrable G) (hG0 : ∀z,0≤G z)
    (hG1 : Integrable (fun z : ℝ=>G z*|z|))
    (hV : Integrable V)
    (htrans : ∀z : ℝ,(∫x : ℝ,‖V x-V (x-z)‖)≤K*|z|) :
    (∫x : ℝ,‖((∫z : ℝ,G z):ℂ)*V x-smooth G V x‖)
      ≤K*(∫z : ℝ,G z*|z|) := by
  have hc := smooth_joint_integrable hG hV
  have hconst : Integrable (fun p : ℝ×ℝ=>(G p.2:ℂ)*V p.1) (volume.prod volume) :=
    (hG.ofReal.mul_prod hV).swap
  have hj : Integrable (fun p : ℝ×ℝ=>(G p.2:ℂ)*(V p.1-V (p.1-p.2)))
      (volume.prod volume) := by
    convert hconst.sub hc using 1
    ext p
    simp only [Pi.sub_apply,mul_sub]
  have he : ∀ᵐ x : ℝ, ((∫z : ℝ,G z):ℂ)*V x-smooth G V x =
      ∫z : ℝ,(G z:ℂ)*(V x-V (x-z)) := by
    filter_upwards [hc.prod_right_ae] with x hx
    change _ - (∫z : ℝ,(G z:ℂ)*V (x-z)) = _
    calc
      _ = (∫z : ℝ,(G z:ℂ)*V x) - (∫z : ℝ,(G z:ℂ)*V (x-z)) := by
        rw [MeasureTheory.integral_mul_const,integral_complex_ofReal]
      _ = ∫z : ℝ,(G z:ℂ)*V x-(G z:ℂ)*V (x-z) :=
        (integral_sub (hG.ofReal.mul_const (V x)) hx).symm
      _ = _ := by simp only [mul_sub]
  calc
    _ ≤ ∫x : ℝ,∫z : ℝ,‖(G z:ℂ)*(V x-V (x-z))‖ := by
      apply integral_mono_ae
        ((hV.const_mul _).sub (smooth_integrable hG hV)).norm hj.norm.integral_prod_left
      filter_upwards [he] with x hx
      dsimp only [Pi.sub_apply]
      rw [hx]
      exact norm_integral_le_integral_norm _
    _ = ∫z : ℝ,G z*(∫x : ℝ,‖V x-V (x-z)‖) := by
      rw [integral_integral_swap hj.norm]
      congr 1
      funext z
      simp_rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hG0 z),MeasureTheory.integral_const_mul]
    _ ≤ ∫z : ℝ,K*(G z*|z|) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun z=>mul_nonneg (hG0 z) (integral_nonneg fun x=>norm_nonneg _)))
        (hG1.const_mul K)
      filter_upwards [] with z
      have hh := mul_le_mul_of_nonneg_left (htrans z) (hG0 z)
      convert hh using 1
      ring
    _ = _ := integral_const_mul _ _

lemma smooth_l1_le {G : ℝ→ℝ} {V : ℝ→ℂ}
    (hG : Integrable G) (hG0 : ∀z,0≤G z) (hV : Integrable V) :
    (∫x : ℝ,‖smooth G V x‖)≤(∫z : ℝ,G z)*(∫x : ℝ,‖V x‖) := by
  have hc := smooth_joint_integrable hG hV
  calc
    _ ≤ ∫x : ℝ,∫z : ℝ,‖(G z:ℂ)*V (x-z)‖ :=
      integral_mono (smooth_integrable hG hV).norm hc.norm.integral_prod_left
        (fun x=>norm_integral_le_integral_norm _)
    _ = _ := by
      rw [integral_integral_swap hc.norm]
      have he (z : ℝ) : (∫x : ℝ,‖(G z:ℂ)*V (x-z)‖)=G z*(∫x : ℝ,‖V x‖) := by
        simp_rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hG0 z)]
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact integral_sub_right_eq_self (fun x : ℝ=>‖V x‖) z
      simp_rw [he]
      exact integral_mul_const _ _

end OrdinarySharpWindow

end

end OAI

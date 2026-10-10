import Mathlib
import OAI.Probability.Perceptron.Variational.HeatLogBCF

namespace OAI

noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def weightedDerivative (w : ℝ→ᵇℝ) (hw : HasCompactSupport (w : ℝ→ℝ)) (k : ℕ) : ℝ→ᵇℝ :=
  ofCompactSupport (fun z => z^k*w z) ((continuous_id.pow k).mul w.continuous) hw.mul_left

lemma weightedDerivative_bound (w : ℝ→ᵇℝ) (hw : HasCompactSupport (w : ℝ→ℝ)) (k : ℕ) (z : ℝ) :
    |z^k*w z|≤‖weightedDerivative w hw k‖ := (weightedDerivative w hw k).norm_coe_le_norm z

lemma Jet3.dilation_has1 (g : Jet3) (s t : ℝ) :
    HasDerivAt (fun u => g.f (Real.exp u*s)) (Real.exp t*s*g.d1 (Real.exp t*s)) t := by
  simpa only [Function.comp_def, mul_comm] using (g.has1 (Real.exp t*s)).comp t ((Real.hasDerivAt_exp t).mul_const s)

lemma Jet3.dilation_has2 (g : Jet3) (s t : ℝ) :
    HasDerivAt (fun u => Real.exp u*s*g.d1 (Real.exp u*s))
      (Real.exp t*s*g.d1 (Real.exp t*s)+(Real.exp t*s)^2*g.d2 (Real.exp t*s)) t := by
  have h := ((Real.hasDerivAt_exp t).mul_const s).mul
    ((g.has2 (Real.exp t*s)).comp t ((Real.hasDerivAt_exp t).mul_const s))
  convert h using 1 <;> first | rfl | (simp only [Function.comp_apply]; ring)

lemma Jet3.dilation_remainder (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ)) (s t : ℝ) :
    |g.f (Real.exp t*s)-g.f s-t*s*g.d1 s|≤
      (‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖)*t^2/2 := by
  have hd : deriv (fun u => g.f (Real.exp u*s))=fun u => Real.exp u*s*g.d1 (Real.exp u*s) :=
    funext fun u => (g.dilation_has1 s u).deriv
  have hd2 : iteratedDeriv 2 (fun u => g.f (Real.exp u*s))=
      fun u => Real.exp u*s*g.d1 (Real.exp u*s)+(Real.exp u*s)^2*g.d2 (Real.exp u*s) := by
    rw [iteratedDeriv_succ,iteratedDeriv_one,hd]
    exact funext fun u => (g.dilation_has2 s u).deriv
  have hc : ContDiff ℝ 2 (fun u => g.f (Real.exp u*s)) :=
    (g.contDiff.of_le (by norm_num)).comp (Real.contDiff_exp.mul contDiff_const)
  have ht := first_order_taylor_bound hc _ (fun u => by
    rw [hd2]
    apply (abs_add_le _ _).trans
    simpa only [pow_one] using add_le_add
      (weightedDerivative_bound g.d1 h1 1 (Real.exp u*s)) (weightedDerivative_bound g.d2 h2 2 (Real.exp u*s))) 0 t
  simp only [hd,Real.exp_zero,one_mul,sub_zero] at ht
  convert ht using 1; ring_nf

lemma dilation_lipschitz_bound (w w' : ℝ→ᵇℝ) (hw' : HasCompactSupport (w' : ℝ→ℝ))
    (hd : ∀ x,HasDerivAt (w : ℝ→ℝ) (w' x) x) (s t : ℝ) :
    |w (Real.exp t*s)-w s|≤‖weightedDerivative w' hw' 1‖*|t| := by
  have hh u : HasDerivAt (fun u => w (Real.exp u*s)) (Real.exp u*s*w' (Real.exp u*s)) u := by
    simpa only [Function.comp_def, mul_comm] using (hd (Real.exp u*s)).comp u ((Real.hasDerivAt_exp u).mul_const s)
  have hl := lipschitzWith_of_nnnorm_deriv_le (C:=‖weightedDerivative w' hw' 1‖₊)
    (fun u => (hh u).differentiableAt) (fun u => by
      apply NNReal.coe_le_coe.mp
      rw [coe_nnnorm,Real.norm_eq_abs,(hh u).deriv]
      simpa only [pow_one,coe_nnnorm] using weightedDerivative_bound w' hw' 1 (Real.exp u*s))
  simpa only [Real.dist_eq,sub_zero,Real.exp_zero,one_mul,coe_nnnorm] using hl.dist_le_mul t 0

theorem Jet3.cavity_log_dilation_expansion (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (s t u : ℝ) :
    |g.f (Real.exp t*s+u)-g.f s-t*s*g.d1 s-u*g.d1 s-u^2/2*g.d2 s|≤
      (‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖)*t^2/2+
      ‖weightedDerivative g.d2 h2 1‖*|t| * |u|+
      ‖weightedDerivative g.d3 h3 1‖*|t| * u^2/2+‖g.d3‖*|u| ^3/6 := by
  have ht := second_order_taylor_bound g.contDiff ‖g.d3‖ (fun z => by rw [g.deriv3_eq]; exact g.d3.norm_coe_le_norm z)
    (Real.exp t*s) (Real.exp t*s+u)
  simp only [g.deriv_eq,g.deriv2_eq,add_sub_cancel_left] at ht
  have hd := g.dilation_remainder h1 h2 s t
  have h₁ := dilation_lipschitz_bound g.d1 g.d2 h2 g.has2 s t
  have h₂ := dilation_lipschitz_bound g.d2 g.d3 h3 g.has3 s t
  calc
    _ = |(g.f (Real.exp t*s+u)-g.f (Real.exp t*s)-g.d1 (Real.exp t*s)*u-g.d2 (Real.exp t*s)*u^2/2)+
      (g.f (Real.exp t*s)-g.f s-t*s*g.d1 s)+
      (g.d1 (Real.exp t*s)-g.d1 s)*u+(g.d2 (Real.exp t*s)-g.d2 s)*u^2/2| := by congr 1; ring
    _ ≤ |g.f (Real.exp t*s+u)-g.f (Real.exp t*s)-g.d1 (Real.exp t*s)*u-g.d2 (Real.exp t*s)*u^2/2|+
      |g.f (Real.exp t*s)-g.f s-t*s*g.d1 s|+
      |(g.d1 (Real.exp t*s)-g.d1 s)*u|+|(g.d2 (Real.exp t*s)-g.d2 s)*u^2/2| := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      rw [abs_mul,abs_div,abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ)≤2),sq_abs]
      have h₁u := mul_le_mul_of_nonneg_right h₁ (abs_nonneg u)
      have h₂u := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h₂ (sq_nonneg u)) (by norm_num : (0:ℝ)≤2)
      linarith

end SphericalPerceptronFreeEnergy
end

end OAI

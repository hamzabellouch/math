import Mathlib
import OAI.Probability.SKValue.Evolution.HeatContinuity

namespace OAI

section

open Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue

lemma BoundedSmooth.comp_mul {f : ℝ → ℝ} (hf : BoundedSmooth f) (a : ℝ) :
    BoundedSmooth (fun x ↦ f (a*x)) := by
  refine ⟨hf.smooth.comp (contDiff_const.mul contDiff_id),?_⟩
  intro n
  obtain ⟨C,hC,hb⟩ := hf.bound n
  refine ⟨|a|^n*C,by positivity,?_⟩
  intro x
  rw [iteratedDeriv_comp_const_mul (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))]
  rw [abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (hb _) (by positivity)

lemma SmoothTerminal.deriv_abs_le {f : ℝ → ℝ} (hf : SmoothTerminal f) (x : ℝ) :
    |deriv f x|≤1 := by
  simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hf.lipschitz (x₀ := x)

lemma SmoothTerminal.linear {f g : ℝ → ℝ} (hf : SmoothTerminal f) (hg : SmoothTerminal g)
    {a b : ℝ} (hab : |a|+|b|≤1) : SmoothTerminal (fun x ↦ a*f x+b*g x) := by
  have hfd := hf.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hgd := hg.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hd : deriv (fun x ↦ a*f x+b*g x)=fun x ↦ a*deriv f x+b*deriv g x :=
    funext (fun x ↦ (((hfd x).hasDerivAt.const_mul a).add ((hgd x).hasDerivAt.const_mul b)).deriv)
  have hs : ContDiff ℝ ∞ (fun x ↦ a*f x+b*g x) := (contDiff_const.mul hf.smooth).add (contDiff_const.mul hg.smooth)
  refine ⟨?_,hs,?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne')
    intro x
    have hh : |a*deriv f x+b*deriv g x|≤1 := calc
      _ ≤ |a*deriv f x|+|b*deriv g x| := abs_add_le _ _
      _ = |a| *|deriv f x|+|b| *|deriv g x| := by simp only [abs_mul]
      _ ≤ |a| *1+|b| *1 := add_le_add
        (mul_le_mul_of_nonneg_left (hf.deriv_abs_le x) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (hg.deriv_abs_le x) (abs_nonneg b))
      _ ≤ 1 := by simpa only [mul_one] using hab
    rw [hd]
    exact_mod_cast hh
  · rw [hd]
    exact (hf.jets.const_mul a).add (hg.jets.const_mul b)

lemma SmoothTerminal.neg {f : ℝ → ℝ} (hf : SmoothTerminal f) :
    SmoothTerminal (fun x ↦ -f x) := by
  simpa only [neg_one_mul,zero_mul,add_zero] using hf.linear hf (a := -1) (b := 0) (by norm_num)

lemma SmoothTerminal.comp_mul {f : ℝ → ℝ} (hf : SmoothTerminal f) {a : ℝ}
    (ha : |a|≤1) : SmoothTerminal (fun x ↦ f (a*x)) := by
  have hfd := hf.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hd : deriv (fun x ↦ f (a*x))=fun x ↦ a*deriv f (a*x) := by
    funext x
    convert! ((hfd (a*x)).hasDerivAt.comp x ((hasDerivAt_id x).const_mul a)).deriv using 1
    simp only [mul_one]
    ring
  have hs : ContDiff ℝ ∞ (fun x ↦ f (a*x)) := hf.smooth.comp (contDiff_const.mul contDiff_id)
  refine ⟨?_,hs,?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne')
    intro x
    have hh : |a*deriv f (a*x)|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hf.deriv_abs_le _) (abs_nonneg a)).trans (by simpa only [mul_one] using ha)
    rw [hd]
    exact_mod_cast hh
  · rw [hd]
    exact (hf.jets.comp_mul a).const_mul a

end SKValue

end

end OAI

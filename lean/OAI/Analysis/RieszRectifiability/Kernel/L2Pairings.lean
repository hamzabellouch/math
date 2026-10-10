import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FiniteStepLp

namespace OAI

/-!
# Integral pairings of real L² functions

The L² inner product agrees with integration of pointwise products. Subtraction and
Cauchy–Schwarz then bound differences of pairings by squared L² errors.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem real_scalar_inner_mul (a b : ℝ) : inner ℝ a b = a * b := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  simp only [← pow_two, Real.norm_eq_abs, sq_abs]
  ring

theorem toLp_inner_eq_integral (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy, real_scalar_inner_mul]

theorem integral_mul_cauchy_schwarz_sq (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [toLp_norm_sq_eq_integral, toLp_norm_sq_eq_integral] at h
  simpa only [toLp_inner_eq_integral, pow_two] using! h

theorem integral_mul_sub_eq (μ : Measure X) (f g ψ : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hψ : MemLp ψ 2 μ) :
    (∫ x, (f x - g x) * ψ x ∂μ) =
      (∫ x, f x * ψ x ∂μ) - (∫ x, g x * ψ x ∂μ) := by
  have hfp : MemLp (fun x => f x * ψ x) 1 μ := hf.mul hψ
  have hgp : MemLp (fun x => g x * ψ x) 1 μ := hg.mul hψ
  simp_rw [sub_mul]
  exact integral_sub (memLp_one_iff_integrable.mp hfp) (memLp_one_iff_integrable.mp hgp)

theorem integral_pairing_difference_sq_le (μ : Measure X) (f g ψ : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hψ : MemLp ψ 2 μ) :
    ((∫ x, f x * ψ x ∂μ) - (∫ x, g x * ψ x ∂μ)) ^ 2 ≤
      (∫ x, (f x - g x) ^ 2 ∂μ) * (∫ x, ψ x ^ 2 ∂μ) := by
  rw [← integral_mul_sub_eq μ f g ψ hf hg hψ]
  exact integral_mul_cauchy_schwarz_sq μ (f - g) ψ (hf.sub hg) hψ

theorem L2_pairing_tendsto (ν : Measure X) (v : ℕ → Lp ℝ 2 ν)
    (limit : Lp ℝ 2 ν) (hv : Tendsto v atTop (𝓝 limit))
    (ψ : X → ℝ) (hψ : MemLp ψ 2 ν) :
    Tendsto (fun k => ∫ x, v k x * ψ x ∂ν)
      atTop (𝓝 (∫ x, limit x * ψ x ∂ν)) := by
  have heq (f : Lp ℝ 2 ν) : inner ℝ f (hψ.toLp ψ) = ∫ x, f x * ψ x ∂ν := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with x hx
    rw [hx, real_scalar_inner_mul]
  simp_rw [← heq]
  exact hv.inner tendsto_const_nhds

end

end RieszRectifiability

end OAI

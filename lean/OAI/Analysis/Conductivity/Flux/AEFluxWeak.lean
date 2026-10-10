import Mathlib
import OAI.Analysis.Conductivity.Flux.C1WeakDivergence

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

theorem C1_divergence_zero_ae_test
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure E) [μ.IsAddHaarMeasure] (v : ι → E) (F : ι → E → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i))
    (ψ : SmoothScalar E) (hc : HasCompactSupport ψ.val)
    (hdiv : ∀ᵐ x ∂μ, x∈Function.support ψ.val → ∑ i, direction (v i) (F i) x = 0) :
    (∫ x, ∑ i, F i x*(smoothDirection (v i) ψ).val x ∂μ) = 0 := by
  have hp := smoothScalar_contDiff ψ
  have hI (i : ι) : Integrable (fun x => F i x*(smoothDirection (v i) ψ).val x) μ :=
    ((hF i).continuous.mul (smoothScalar_contDiff (smoothDirection (v i) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (v i) hc).mul_left
  have hI' (i : ι) : Integrable (fun x => ψ.val x*direction (v i) (F i) x) μ :=
    (hp.continuous.mul (direction_continuous (hF i) _)).integrable_of_hasCompactSupport hc.mul_right
  have hibp (i : ι) : (∫ x, F i x*(smoothDirection (v i) ψ).val x ∂μ) =
      -(∫ x, ψ.val x*direction (v i) (F i) x ∂μ) := by
    have hh := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ)
      (f := F i) (g := ψ.val) (v := v i)
      (show Integrable (fun x => direction (v i) (F i) x*ψ.val x) μ by
        simpa only [mul_comm] using hI' i)
      (hI i)
      (((hF i).continuous.mul hp.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun x _ => ((hF i).differentiable (by norm_num) x).hasFDerivAt)
      (fun x _ => (hp.differentiable (by simp) x).hasFDerivAt)
    change (∫ x, F i x * (fderiv ℝ ψ.val x) (v i) ∂μ) =
      -(∫ x, (fderiv ℝ (F i) x) (v i) * ψ.val x ∂μ) at hh
    simpa only [direction,smoothDirection_apply,mul_comm] using hh
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib,←integral_finsetSum _ (fun i _ => hI' i)]
  have hz : (fun x => ∑ i, ψ.val x*direction (v i) (F i) x) =ᵐ[μ] fun _ => (0:ℝ) := by
    filter_upwards [hdiv] with x hxdiv
    rw [←Finset.mul_sum]
    by_cases hx : x∈Function.support ψ.val
    · rw [hxdiv hx,mul_zero]
    · rw [Function.notMem_support.mp hx,zero_mul]
  rw [integral_congr_ae hz,integral_zero,neg_zero]

end ScalarConductivity

end
end

end OAI

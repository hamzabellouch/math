import OAI.Geometry.RCD.Sobolev.BoundedL2Difference

namespace OAI

/-! # L² difference from a local bound and two square-integrable tails -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem tight_L2_norm_sub_sq_le (f g : Lp ℝ 2 μ)
    (hfi : Integrable f μ) (hgi : Integrable g μ) {S : Set X} (hS : MeasurableSet S)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ.restrict S, |f x| ≤ C) (hg : ∀ᵐ x ∂μ.restrict S, |g x| ≤ C) :
    ‖f-g‖^2 ≤ 2*C*(∫ x, |f x-g x| ∂μ)+
      2*(∫ x in Sᶜ, (f x)^2 ∂μ)+2*(∫ x in Sᶜ, (g x)^2 ∂μ) := by
  have he := Lp.coeFn_sub f g
  have hi : Integrable (fun x => (f x-g x)^2) μ :=
    (Lp.memLp (f-g)).integrable_sq.congr (he.fun_comp fun a : ℝ => a^2)
  have hab : Integrable (fun x => |f x-g x|) μ := (hfi.sub hgi).abs
  have hlocal : (∫ x in S, (f x-g x)^2 ∂μ) ≤ 2*C*(∫ x, |f x-g x| ∂μ) := by
    calc
      _ ≤ ∫ x in S, (2*C)*|f x-g x| ∂μ := by
        apply integral_mono_ae hi.integrableOn (hab.const_mul (2*C)).integrableOn
        filter_upwards [hf,hg] with x hx hy
        have hh := (abs_sub (f x) (g x)).trans (add_le_add hx hy)
        nlinarith [sq_abs (f x-g x),abs_nonneg (f x-g x)]
      _ = 2*C*(∫ x in S, |f x-g x| ∂μ) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hab (Eventually.of_forall fun x => abs_nonneg _)) (by positivity)
  have htail : (∫ x in Sᶜ, (f x-g x)^2 ∂μ) ≤
      2*(∫ x in Sᶜ, (f x)^2 ∂μ)+2*(∫ x in Sᶜ, (g x)^2 ∂μ) := by
    calc
      _ ≤ ∫ x in Sᶜ, 2*(f x)^2+2*(g x)^2 ∂μ := by
        apply integral_mono hi.integrableOn
          (((Lp.memLp f).integrable_sq.const_mul 2).add ((Lp.memLp g).integrable_sq.const_mul 2)).integrableOn
        intro x
        change (f x-g x)^2 ≤ 2*(f x)^2+2*(g x)^2
        nlinarith [sq_nonneg (f x+g x)]
      _ = _ := by
        rw [integral_add ((Lp.memLp f).integrable_sq.const_mul 2).integrableOn
          ((Lp.memLp g).integrable_sq.const_mul 2).integrableOn,integral_const_mul,integral_const_mul]
  have hnorm : ‖f-g‖^2 = ∫ x, (f x-g x)^2 ∂μ := by
    rw [← integral_sq_Lp μ (f-g)]
    exact integral_congr_ae (he.fun_comp fun a : ℝ => a^2)
  rw [hnorm,← integral_add_compl hS hi]
  linarith

end RegularPointCoordinates

end

end OAI

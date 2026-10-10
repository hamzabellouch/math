import OAI.Analysis.KadisonKastler.HilbertVariance
import Mathlib.Probability.Independence.Integration

namespace OAI

/-! An independent random vector cannot improve the constant L2 approximation. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable {X K : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [TopologicalSpace.SeparableSpace K]

omit [TopologicalSpace.SeparableSpace K] in
theorem independent_L2_inner (f g : Lp K 2 μ) (hfg : IndepFun f g μ) :
    inner ℝ f g = inner ℝ (∫ x, f x ∂μ) (∫ x, g x ∂μ) := by
  rw [L2.inner_def]
  exact hfg.integral_bilin ((Lp.memLp f).integrable (by norm_num))
    ((Lp.memLp g).integrable (by norm_num)) (innerSL ℝ)

theorem independent_L2_centering_le (f g : Lp K 2 μ) (hfg : IndepFun f g μ) :
    ‖f - hilbertConstantL2 μ (∫ x, f x ∂μ)‖ ≤ ‖f - g‖ := by
  let a := hilbertConstantL2 μ (∫ x, f x ∂μ)
  have ha : a =ᵐ[μ] fun _ => ∫ x, f x ∂μ := hilbertConstantL2_ae _
  have haf : (f - a : Lp K 2 μ) =ᵐ[μ] fun x => f x - ∫ x, f x ∂μ := by
    filter_upwards [Lp.coeFn_sub f a, ha] with x hx hax
    rw [hx, Pi.sub_apply, hax]
  have hag : (g - a : Lp K 2 μ) =ᵐ[μ] fun x => g x - ∫ x, f x ∂μ := by
    filter_upwards [Lp.coeFn_sub g a, ha] with x hx hax
    rw [hx, Pi.sub_apply, hax]
  have hsub : IndepFun (f - a : Lp K 2 μ) (g - a : Lp K 2 μ) μ :=
    (hfg.comp (measurable_id.sub measurable_const) (measurable_id.sub measurable_const)).congr
      haf.symm hag.symm
  have hmean : ∫ x, (f - a : Lp K 2 μ) x ∂μ = 0 := by
    rw [integral_congr_ae haf, integral_sub ((Lp.memLp f).integrable (by norm_num))
      (integrable_const _)]
    simp
  have hi : inner ℝ (f - a) (g - a) = 0 := by
    rw [independent_L2_inner _ _ hsub, hmean, inner_zero_left]
  have hn := norm_sub_sq_real (f - a) (g - a)
  have he : (f - a) - (g - a) = f - g := by abel
  rw [he, hi, mul_zero, sub_zero] at hn
  change ‖f - a‖ ≤ ‖f - g‖
  nlinarith [sq_nonneg ‖g - a‖, norm_nonneg (f - a), norm_nonneg (f - g)]

end

end KadisonKastler

end OAI

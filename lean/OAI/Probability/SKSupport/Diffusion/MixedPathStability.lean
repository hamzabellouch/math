import Mathlib
import OAI.Probability.SKSupport.Diffusion.MixedDrift
import OAI.Probability.SKSupport.Diffusion.DiffusionStability

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma mixedDrift_error (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ s x, |compactGradient W β T s x-compactGradient W γ T s x| ≤ δ) :
    ∀ s ∈ Icc (0:ℝ) T, ∀ x,
      |(stripDrift W γ T).f s x-(mixedStripDrift W β γ T).f s x| ≤
        |extend β.val s-extend γ.val s|+γ.val T*δ := by
  intro s hs x
  have hm : |compactGradient W γ T s x-compactMixedGradient W β γ T s x| ≤ δ := by
    have he : compactGradient W γ T s x-compactMixedGradient W β γ T s x=
        -(compactGradient W β T s x-compactGradient W γ T s x)/2 := by unfold compactMixedGradient;ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hh := hd s x
    linarith
  have hc : |compactCoeff γ T s| ≤ γ.val T := by
    rw [abs_of_nonneg (compactCoeff_bounds γ T.property.1 T.property.2 s).1]
    exact (compactCoeff_bounds γ T.property.1 T.property.2 s).2
  have hh := mul_sub_mul_error (b := compactCoeff β T s) hδ hc
    (compactMixedGradient_bound W β γ T.property.1 T.property.2 s x) hm
  simpa only [stripDrift,compactDrift,mixedStripDrift,compactMixedDrift,compactCoeff,stripClamp_eq hs,abs_sub_comm] using hh

lemma mixedPath_error (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ s x, |compactGradient W β T s x-compactGradient W γ T s x| ≤ δ)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) (ξ : Ω) :
    |(mixedStripDrift W β γ T).solution W.driver t ξ-diffusion W γ t ξ| ≤
      2*(coefficientDistance β γ+γ.val T*(T:ℝ)*δ)*Real.exp ((stripDrift W γ T).rate*T) := by
  let e (s : ℝ) := |extend β.val s-extend γ.val s|+γ.val T*δ
  have hei (a b : ℝ) : IntervalIntegrable e volume a b :=
    ((β.integrable.sub γ.integrable).abs.intervalIntegrable).add intervalIntegrable_const
  have hen (s : ℝ) : 0 ≤ e s := add_nonneg (abs_nonneg _) (mul_nonneg (γ.nonneg _) hδ)
  let TT : ℝ≥0 := ⟨T,T.property.1⟩
  have hh := (stripDrift W γ T).solution_stability_integral (mixedStripDrift W β γ T) _ W.driver_progressive TT
    (hei 0 T) (fun s _ => hen s) (Eventually.of_forall (fun s => mixedDrift_error W β γ T hδ hd s)) t ht ξ
  rw [← diffusion_eq_strip W γ T t ht,abs_sub_comm] at hh
  have hi0 : 0 ≤ ∫ s in (0:ℝ)..(T:ℝ), e s := intervalIntegral.integral_nonneg T.property.1 (fun s _ => hen s)
  have hi : (∫ s in (0:ℝ)..(T:ℝ), e s) ≤ coefficientDistance β γ+γ.val T*(T:ℝ)*δ := by
    dsimp only [e,coefficientDistance]
    have hfi : IntervalIntegrable (fun s => |extend β.val s-extend γ.val s|) volume 0 T := (β.integrable.sub γ.integrable).abs.intervalIntegrable
    rw [intervalIntegral.integral_add hfi intervalIntegrable_const,
      intervalIntegral.integral_const]
    have hh := intervalIntegral.integral_mono_interval (a := (0:ℝ)) (b := (T:ℝ)) (c := (0:ℝ)) (d := 1)
      le_rfl T.property.1 T.property.2.le (Eventually.of_forall (fun s => abs_nonneg (extend β.val s-extend γ.val s)))
      ((β.integrable.sub γ.integrable).abs.intervalIntegrable)
    simp only [sub_zero,smul_eq_mul]
    nlinarith only [hh]
  have hex : Real.exp ((stripDrift W γ T).rate*t) ≤ Real.exp ((stripDrift W γ T).rate*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (stripDrift W γ T).rate_pos.le)
  exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left hi (by norm_num)) hex
    (Real.exp_pos _).le (mul_nonneg (by norm_num) (hi0.trans hi)))

end ZeroTemperatureSK

end
end

end OAI

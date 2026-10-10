import Mathlib
import OAI.Probability.SKSupport.Moments.SquareEquation
import OAI.Probability.SKSupport.Control.ValueDifference
import OAI.Probability.SKSupport.Diffusion.MixedDrift

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma differenceField_generator (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (differenceField W β γ hT0 hT1).generator (compactMixedDrift W β γ T) t x =
      -(1/2:ℝ)*(compactCoeff β T t-compactCoeff γ T t)*(compactGradient W γ T t x)^2 := by
  have hb := (((compactGradient_family W β hT0 hT1).regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hg := (((compactGradient_family W γ hT0 hT1).regular t).smooth.differentiable (by simp) x).hasDerivAt
  change deriv (compactDifference W β γ T t) x*compactMixedDrift W β γ T t x+
    (1/2:ℝ)*deriv (deriv (compactDifference W β γ T t)) x+compactDifferenceRate W β γ T t x=_
  have hd := (hb.sub hg).deriv
  change deriv (fun y => compactGradient W β T t y-compactGradient W γ T t y) x=_ at hd
  rw [compactDifference_deriv W β γ hT0 hT1,hd]
  unfold compactDifferenceRate compactValueRate valueRate compactMixedDrift compactMixedGradient
    compactCoeff compactGradient curvature gradient
  ring

def mixedQ (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) (t : ℝ) : ℝ :=
  ∫ ξ, (compactGradient W γ T t ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal t) ξ))^2 ∂W.law

lemma mixedQ_continuous (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) :
    Continuous (mixedQ W β γ T) := by
  convert (mixedStripDrift W β γ T).expected_continuous W
    (compactSquare_family W γ T.property.1 T.property.2)
    (compactSquare_continuous W γ T.property.1 T.property.2) using 1
  funext t
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [compactSquare,pow_two]

lemma mixedQ_bounds (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) (t : ℝ) :
    0 ≤ mixedQ W β γ T t ∧ mixedQ W β γ T t ≤ 1 := by
  let := W.isProbability
  have hi : Integrable (fun ξ => (compactGradient W γ T t
      ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal t) ξ))^2) W.law := by
    simpa only [pow_two,compactSquare] using
      integrable_family_comp (P := W.law) (compactSquare_family W γ T.property.1 T.property.2) t
        ((mixedStripDrift W β γ T).solution_measurable W (Real.toNNReal t))
  refine ⟨integral_nonneg (fun ξ => sq_nonneg _),?_⟩
  calc
    mixedQ W β γ T t ≤ ∫ _ : Ω, (1:ℝ) ∂W.law := integral_mono hi (integrable_const _) (fun ξ => by
      have hh := compactGradient_bound W γ T.property.1 T.property.2 t
        ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal t) ξ)
      rw [abs_le] at hh
      nlinarith)
    _ = 1 := by simp

lemma mixed_difference_right (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time)
    (s : ℝ≥0) (hs : (s:ℝ) < T) :
    HasDerivWithinAt ((differenceField W β γ T.property.1 T.property.2).expected
      (mixedStripDrift W β γ T) W)
      (-(1/2:ℝ)*(compactCoeff β T s-compactCoeff γ T s)*mixedQ W β γ T s) (Ioi (s:ℝ)) s := by
  have hh := (differenceField W β γ T.property.1 T.property.2).expected_hasDerivWithinAt_right
    (mixedStripDrift W β γ T) W s hs (mixedStripDrift_pathDrift_right W β γ T s)
  have he : (∫ ξ, (differenceField W β γ T.property.1 T.property.2).generator
      (mixedStripDrift W β γ T).f s ((mixedStripDrift W β γ T).solution W.driver s ξ) ∂W.law) =
      -(1/2:ℝ)*(compactCoeff β T s-compactCoeff γ T s)*mixedQ W β γ T s := by
    simp only [mixedStripDrift,differenceField_generator,mixedQ,Real.toNNReal_coe]
    rw [integral_const_mul]
  rw [he] at hh
  exact hh

lemma mixed_difference_zero (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) :
    (differenceField W β γ T.property.1 T.property.2).expected (mixedStripDrift W β γ T) W 0 =
      value W β 0 0-value W γ 0 0 := by
  let := W.isProbability
  have hx (ξ : Ω) : (mixedStripDrift W β γ T).solution W.driver 0 ξ=0 := by
    rw [(mixedStripDrift W β γ T).solution_eq _ W.driver_progressive]
    simp only [NNReal.coe_zero,intervalIntegral.integral_same,W.driver_zero,add_zero]
  simp [TimeField.expected,differenceField,Real.toNNReal_zero,hx,compactDifference,
    stripClamp_eq ⟨le_rfl,T.property.1⟩]

lemma mixed_difference_integral (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) :
    value W β 0 0-value W γ 0 0 =
      (differenceField W β γ T.property.1 T.property.2).expected (mixedStripDrift W β γ T) W T+
      (1/2:ℝ)*(∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*mixedQ W β γ T s) := by
  let f := (differenceField W β γ T.property.1 T.property.2)
  have hc : ContinuousOn (f.expected (mixedStripDrift W β γ T) W) (Icc (0:ℝ) T) :=
    (f.expected_continuous (mixedStripDrift W β γ T) W).continuousOn
  have hi : IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*mixedQ W β γ T s) volume 0 T :=
    ((β.integrable.sub γ.integrable).intervalIntegrable).mul_continuousOn
      (mixedQ_continuous W β γ T).continuousOn
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le T.property.1 hc
    (f' := fun s => -(1/2:ℝ)*((extend β.val s-extend γ.val s)*mixedQ W β γ T s))
    (fun s hs => by
      have hh := mixed_difference_right W β γ T (Real.toNNReal s)
        (by rw [Real.coe_toNNReal _ hs.1.le];exact hs.2)
      simpa only [Real.coe_toNNReal _ hs.1.le,compactCoeff,stripClamp_eq ⟨hs.1.le,hs.2.le⟩,mul_assoc] using hh)
    (hi.const_mul _)
  rw [intervalIntegral.integral_const_mul,mixed_difference_zero] at hh
  dsimp only [f] at hh ⊢
  linarith

lemma mixed_difference_terminal_bound (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) :
    |(differenceField W β γ T.property.1 T.property.2).expected (mixedStripDrift W β γ T) W T| ≤
      (3/2:ℝ)*(∫ s in (T:ℝ)..1, |extend β.val s-extend γ.val s|) := by
  let := W.isProbability
  change |∫ ξ, compactDifference W β γ T T _ ∂W.law| ≤ _
  rw [← Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le_const (μ := W.law)
    (f := fun ξ => compactDifference W β γ T T ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal T) ξ))
    (C := (3/2:ℝ)*(∫ s in (T:ℝ)..1, |extend β.val s-extend γ.val s|)) (by
      filter_upwards [] with ξ
      simp only [compactDifference,stripClamp_eq ⟨T.property.1,le_rfl⟩,Real.norm_eq_abs]
      exact value_coefficient_stability W β γ T _ T.property.2.le)
  simpa using hh

end ZeroTemperatureSK

end
end

end OAI

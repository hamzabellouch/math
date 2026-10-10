import Mathlib
import OAI.Probability.SKValue.Equations.ThirdOrderRemainderBound

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma value_euler_one_step {V : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {t δ x z G K L : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hG : 0≤G) (hK : 0≤K) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0≤γ t) (hγG : γ t≤G)
    (hu : |deriv (V t) x|≤1) (hsmooth : ContDiff ℝ 3 (V t))
    (ha : |deriv (deriv (V t)) x|≤K)
    (hthird : ∀ y, |iteratedDeriv 3 (V t) y|≤K)
    (hp : ∀ s ∈ Icc t (t+δ), ∀ y, |(1/2 : ℝ)*(deriv (V s) y)^2|≤K)
    (haLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |deriv (deriv (V s)) y-deriv (deriv (V t)) x|≤L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |(1/2 : ℝ)*(deriv (V s) y)^2-(1/2 : ℝ)*(deriv (V t) x)^2|≤L*(|s-t|+|y-x|))
    (haint : ∀ y, IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ))
    (hpint : ∀ y, IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) y)^2)) volume t (t+δ))
    (hPDE : ∀ y, V (t+δ) y-V t y =
      -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) y+γ s*((1/2 : ℝ)*(deriv (V s) y)^2))) :
    let d := Real.sqrt δ*z+δ*γ t*deriv (V t) x
    |V (t+δ) (x+d)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)-
      (1/2 : ℝ)*δ*γ t*(deriv (V t) x)^2| ≤
    δ*Real.sqrt δ*(K*(|z|+G)^3+(1/2+G)*L*(1+|z|+G)+K*G*(|z|+G/2))+
      δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*γ t*deriv (V t) x
  have htm := gradient_generator_quadrature
    (b := fun s y ↦ deriv (deriv (V s)) y)
    (p := fun s y ↦ (1/2 : ℝ)*(deriv (V s) y)^2) (y := x+d)
    hδ hG hK hL hγ hγ0 hγG
    (fun s hs ↦ hp s hs _) (fun s hs ↦ haLip s hs _) (fun s hs ↦ hpLip s hs _)
    (haint _) (hpint _)
  have ht : |(V (t+δ) (x+d)-V t x+deriv (V t) x-
        (1/2 : ℝ)*δ*γ t*(deriv (V t) x)^2)-
      (V t (x+d)-V t x+deriv (V t) x)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*deriv (V t) x*deriv (V t) x)| ≤
      δ*(((1/2 : ℝ)+G)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq : (V (t+δ) (x+d)-V t x+deriv (V t) x-
        (1/2 : ℝ)*δ*γ t*(deriv (V t) x)^2)-
      (V t (x+d)-V t x+deriv (V t) x)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*deriv (V t) x*deriv (V t) x) =
      (V (t+δ) (x+d)-V t (x+d))+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) := by ring
    rw [heq,hPDE]
    rw [show -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
        γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))+
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) =
        -((∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
        γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))-
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2))) by ring,
      abs_neg]
    simpa only [add_sub_cancel_left] using htm
  have hs : |(V t (x+d)-V t x+deriv (V t) x)-deriv (V t) x-
      deriv (V t) x*d-(1/2 : ℝ)*deriv (deriv (V t)) x*d^2| ≤ K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound hsmooth hK hthird x d
  have hh := euler_cubic_remainder hδ hδ1 hG hK (by positivity : 0≤(1/2+G)*L)
    (by rwa [abs_of_nonneg hγ0]) hu ha hs ht
  convert hh using 1
  congr 1
  dsimp only [d]
  ring

end SKValue

end

end OAI

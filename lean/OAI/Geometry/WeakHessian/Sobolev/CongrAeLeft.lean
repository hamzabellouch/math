import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SubConst
import OAI.Geometry.WeakHessian.LocalBounds.RelaxedDomain

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian

section UpperGradientCongruence
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
lemma IsLocalWeakUpperGradient.congr_ae_left {f g D : X → ℝ}
    (hf : IsLocalWeakUpperGradient m f D) (hfg : f =ᵐ[m] g) :
    IsLocalWeakUpperGradient m g D := by
  refine ⟨hf.1,hf.2.1,fun π hπ hb => ?_⟩
  have he : (fun γ : Curve X => ENNReal.ofReal |f (γ timeOne)-f (γ timeZero)|)
      =ᵐ[π] (fun γ : Curve X => ENNReal.ofReal |g (γ timeOne)-g (γ timeZero)|) := by
    filter_upwards [hπ.ae_eval_of_ae hfg timeOne,hπ.ae_eval_of_ae hfg timeZero] with γ h1 h0
    rw [h1,h0]
  rw [← lintegral_congr_ae he]
  exact hf.2.2 π hπ hb

omit [BorelSpace X] in
lemma IsLocalWeakUpperGradient.normalContraction {f D : X → ℝ}
    (hf : IsLocalWeakUpperGradient m f D) {η : ℝ → ℝ} (hη : LipschitzWith 1 η) :
    IsLocalWeakUpperGradient m (η ∘ f) D := by
  refine ⟨hf.1,hf.2.1,fun π hπ hb => ?_⟩
  apply le_trans (lintegral_mono (fun γ => ?_)) (hf.2.2 π hπ hb)
  apply ENNReal.ofReal_le_ofReal
  simpa only [Function.comp_apply, Real.dist_eq, NNReal.coe_one, one_mul] using
    hη.dist_le_mul (f (γ timeOne)) (f (γ timeZero))

end UpperGradientCongruence

open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X} [IsProbabilityMeasure ν]

lemma CurvatureDimension.reference_cheegerEnergy_le_weak_bounded {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ))
    (k : ℕ) (hfb : ∀ᵐ x ∂ν,|f x| ≤ (k:ℝ)) :
    cheegerEnergy ν (f : X → ℝ) ≤ ENNReal.ofReal (‖W‖^2/2) := by
  choose v D h using fun n : ℕ => exists_relaxedProx f (t := 1/((n:ℝ)+1)) (by positivity)
  have hconv : Tendsto v atTop (𝓝 f) :=
    relaxedProx_tendsto f v D _ tendsto_one_div_add_atTop_nhds_zero_nat h
  apply (lowerSemicontinuous_cheegerEnergy.isClosed_preimage (ENNReal.ofReal (‖W‖^2/2))).mem_of_tendsto hconv
  apply Eventually.of_forall
  intro n
  have H := hcd.prox_gradient_norm_le hν (h n) (by positivity) k hfb hf
  exact (relaxedGraph_energy_le (h n).graph).trans (ENNReal.ofReal_le_ofReal (by
    change ‖D n‖^2/2 ≤ ‖W‖^2/2
    nlinarith [norm_nonneg (D n),norm_nonneg W]))

lemma CurvatureDimension.reference_cheegerEnergy_le_weak {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    cheegerEnergy ν (f : X → ℝ) ≤ ENNReal.ofReal (‖W‖^2/2) := by
  let fn : ℕ → Lp ℝ 2 ν := fun n => (realClip_lipschitz n).compLp (realClip_zero n) f
  have hw (n : ℕ) : IsLocalWeakUpperGradient ν (fn n : X → ℝ) (W : X → ℝ) :=
    (hf.normalContraction (realClip_lipschitz n)).congr_ae_left
      ((realClip_lipschitz n).coeFn_compLp (realClip_zero n) f).symm
  have hb (n : ℕ) : ∀ᵐ x ∂ν,|fn n x| ≤ (n:ℝ) := by
    filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) f] with x hx
    rw [show fn n x = realClip n (f x) from hx]
    exact realClip_abs_le n (f x)
  exact (lowerSemicontinuous_cheegerEnergy.isClosed_preimage
    (ENNReal.ofReal (‖W‖^2/2))).mem_of_tendsto (realClip_tendsto_Lp f)
      (Eventually.of_forall fun n => hcd.reference_cheegerEnergy_le_weak_bounded hν (hw n) n (hb n))
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI

import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma bilinear_metric_speed_of_square {g : E →L[ℝ] E →L[ℝ] ℝ}
    {f : ℝ → E} {a k : ℝ} (hf : ContDiffAt ℝ ∞ f a) (h0 : f a = 0)
    (he : (fun t => g (f t) (f t)) =ᶠ[𝓝 a] (fun t => k*(t-a)^2)) :
    g (deriv f a) (deriv f a) = k := by
  have hfd : ∀ᶠ t in 𝓝 a, DifferentiableAt ℝ f t := ((hf.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).eventually (by simp)).mono
    (fun _ ht => ht.differentiableAt (by norm_num))
  have hde : (fun t => g (f t) (deriv f t) + g (deriv f t) (f t)) =ᶠ[𝓝 a]
      (fun t => 2*k*(t-a)) := by
    filter_upwards [hfd,he.eventuallyEq_nhds] with t ht heq
    have h₁ := ((g.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).clm_apply ht.hasDerivAt)
    have h₂ := ((((hasDerivAt_id t).sub_const a).pow 2).const_mul k)
    have hh := (h₁.congr_of_eventuallyEq heq.symm).unique h₂
    norm_num only [Function.comp_apply, Nat.reduceSub, pow_one, id_eq, mul_one, Nat.cast_ofNat] at hh
    linarith
  have hd : HasDerivAt (deriv f) (deriv (deriv f) a) a :=
    ((hf.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hf' := (hf.differentiableAt (by simp)).hasDerivAt
  have h₁ := ((g.hasFDerivAt.comp_hasDerivAt a hf').clm_apply hd).add
    ((g.hasFDerivAt.comp_hasDerivAt a hd).clm_apply hf')
  have h₂ := (((hasDerivAt_id a).sub_const a).const_mul (2*k))
  have hh := (h₁.congr_of_eventuallyEq hde.symm).unique h₂
  simp only [Function.comp_apply,h0,map_zero,zero_apply,add_zero,zero_add,mul_one] at hh
  linarith
end WeakMTWTransport

end

end OAI

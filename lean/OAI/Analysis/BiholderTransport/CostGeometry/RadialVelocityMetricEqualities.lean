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
lemma radial_velocity_of_metric_equalities {g : E →L[ℝ] E →L[ℝ] ℝ}
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) (hs : ∀ v w, g v w = g w v)
    {u V : E} {s τ k : ℝ} (hu : g u u = k^2)
    (hV : τ^2*g V V = s^2*k^2) (hm : τ*g V u = s*k^2) :
    s • u = τ • V := by
  have hz : g (s • u - τ • V) (s • u - τ • V) = 0 := by
    simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul]
    rw [hs u V,hu]
    nlinarith [congrArg (fun z : ℝ => s*z) hm]
  by_contra he
  have hpos := hp (s • u - τ • V) (sub_ne_zero.mpr he)
  linarith

lemma bilinear_metric_radial_derivative {g : E →L[ℝ] E →L[ℝ] ℝ}
    (hs : ∀ u v, g u v = g v u) {f : ℝ → E} {s a τ k : ℝ}
    (hf : DifferentiableAt ℝ f s)
    (he : (fun t => τ^2*g (f t) (f t)) =ᶠ[𝓝 s] (fun t => (t-a)^2*k^2)) :
    τ^2*g (f s) (deriv f s) = (s-a)*k^2 := by
  have hL := (((g.hasFDerivAt.comp_hasDerivAt s hf.hasDerivAt).clm_apply
    hf.hasDerivAt).const_mul (τ^2))
  have hR := (((hasDerivAt_id s).sub_const a).pow 2).mul_const (k^2)
  have H := (hL.congr_of_eventuallyEq he.symm).unique hR
  simp only [Function.comp_apply, Nat.reduceSub, pow_one, id_eq, mul_one,
    Nat.cast_ofNat] at H
  rw [hs (deriv f s) (f s)] at H
  linarith
end WeakMTWTransport

end

end OAI

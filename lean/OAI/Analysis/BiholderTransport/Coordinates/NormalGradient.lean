import Mathlib
import OAI.Analysis.BiholderTransport.Volume.RadialCalibration

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

lemma normal_action_hasFDerivAt
    (e : OpenPartialHomeomorph E E) {y : E} (hy : y ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm y)) (hi : DifferentiableAt ℝ e.symm y)
    (g₀ g₁ : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ u v, g₀ u v = g₀ v u)
    (V : E) (τ : ℝ)
    (hgauss : ∀ w, g₁ V ((fderiv ℝ e (e.symm y)) w) = τ * g₀ (e.symm y) w) :
    HasFDerivAt (fun z => (τ^2/2) * g₀ (e.symm z) (e.symm z))
      (τ • g₁ V) y := by
  have hg := (((g₀.hasFDerivAt.comp y hi.hasFDerivAt).clm_apply hi.hasFDerivAt).const_mul (τ^2/2))
  convert! hg using 1
  ext w
  have hd := congrArg (fun L : E →L[ℝ] E => L w)
    (fderiv_partial_homeomorph_right_inverse e hy he hi)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hd
  have hG := hgauss ((fderiv ℝ e.symm y) w)
  rw [hd] at hG
  simp only [smul_apply,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,smul_eq_mul,Function.comp_apply]
  rw [hsym ((fderiv ℝ e.symm y) w) (e.symm y)]
  rw [hG]
  ring

end WeakMTWTransport

end

end OAI

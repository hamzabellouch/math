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

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionalDerivative (f : E → F) (v : E) (x : E) : F := fderiv ℝ f x v

lemma hasFDerivAt_directionalDerivative {f : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    HasFDerivAt (directionalDerivative f v)
      ((ContinuousLinearMap.apply ℝ F v) ∘L fderiv ℝ (fderiv ℝ f) x) x := by
  exact (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x
    ((hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiableAt (by simp)).hasFDerivAt

lemma directionalDerivative_commute {f : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (u v : E) :
    directionalDerivative (directionalDerivative f u) v x =
      directionalDerivative (directionalDerivative f v) u x := by
  change (fderiv ℝ (directionalDerivative f u) x) v =
    (fderiv ℝ (directionalDerivative f v) x) u
  rw [(hasFDerivAt_directionalDerivative hf u).fderiv,
    (hasFDerivAt_directionalDerivative hf v).fderiv]
  exact (hf.isSymmSndFDerivAt (by simp)).eq v u

lemma contDiffAt_directionalDerivative {f : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (directionalDerivative f v) x :=
  (ContinuousLinearMap.apply ℝ F v).contDiff.contDiffAt.comp x
    (hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp))

lemma hasDerivAt_slice_left {f : ℝ × ℝ → F} {t s : ℝ}
    (hf : DifferentiableAt ℝ f (t,s)) :
    HasDerivAt (fun q => f (q,s)) (directionalDerivative f (1,0) (t,s)) t := by
  exact hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))

lemma hasDerivAt_slice_right {f : ℝ × ℝ → F} {t s : ℝ}
    (hf : DifferentiableAt ℝ f (t,s)) :
    HasDerivAt (fun q => f (t,q)) (directionalDerivative f (0,1) (t,s)) s := by
  exact hf.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_const s t).prodMk (hasDerivAt_id s))

end WeakMTWTransport

end

end OAI

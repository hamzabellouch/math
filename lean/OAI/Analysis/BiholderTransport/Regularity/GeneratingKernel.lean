import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.Hessian

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

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma localMin_generating_kernel {B : E×F → ℝ} {Q : E → F} {p w : E}
    (hB : ContDiffAt ℝ 2 B (p,Q p)) (hmin : IsLocalMin B (p,Q p))
    (hQ : DifferentiableAt ℝ Q p)
    (hstat : ∀ᶠ v in 𝓝 p, ∀ a : E, fderiv ℝ B (v,Q v) (a,0) = 0)
    (hker : fderiv ℝ Q p w = 0) :
    fderiv ℝ (fderiv ℝ B) (p,Q p) (w,0) = 0 := by
  let G : E → E×F := fun v => (v,Q v)
  let G' : E →L[ℝ] E×F := (ContinuousLinearMap.id ℝ E).prod (fderiv ℝ Q p)
  have hG : HasFDerivAt G G' p := (hasFDerivAt_id p).prodMk hQ.hasFDerivAt
  have hDB : HasFDerivAt (fderiv ℝ B) (fderiv ℝ (fderiv ℝ B) (p,Q p)) (G p) :=
    ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hd := ((hDB.comp p hG).clm_apply (hasFDerivAt_const (w,(0:F)) p)).fderiv
  have heq : (fun v => fderiv ℝ B (G v) (w,0)) =ᶠ[𝓝 p] fun _ => (0:ℝ) :=
    hstat.mono (fun _ hv => hv w)
  have hzero : fderiv ℝ (fun v => fderiv ℝ B (G v) (w,0)) p = 0 := by
    rw [heq.fderiv_eq]; exact fderiv_const_apply (0:ℝ)
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L w) (hzero.symm.trans hd)
  have hdiag : fderiv ℝ (fderiv ℝ B) (p,Q p) (w,0) (w,0) = 0 := by
    simpa [G',hker] using hh.symm
  apply ContinuousLinearMap.ext
  intro u
  exact localMin_hessian_null hB hmin hdiag u

lemma localMin_generating_cotangent_kernel {B : E×F → ℝ} {Q : E → F} {p w : E}
    (hB : ContDiffAt ℝ 2 B (p,Q p)) (hmin : IsLocalMin B (p,Q p))
    (hQ : DifferentiableAt ℝ Q p)
    (hstat : ∀ᶠ v in 𝓝 p, ∀ a : E, fderiv ℝ B (v,Q v) (a,0) = 0)
    (hker : fderiv ℝ Q p w = 0) (u : F) :
    fderiv ℝ (fun v => fderiv ℝ B (v,Q v) (0,u)) p w = 0 := by
  have hdB : DifferentiableAt ℝ (fderiv ℝ B) (p,Q p) :=
    (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := ((hdB.hasFDerivAt.comp p
    ((hasFDerivAt_id p).prodMk hQ.hasFDerivAt)).clm_apply
      (hasFDerivAt_const ((0:E),u) p)).fderiv
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L w) hd
  simpa [hker,localMin_generating_kernel hB hmin hQ hstat hker] using hh

end WeakMTWTransport

end

end OAI

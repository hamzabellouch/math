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

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma contDiffAt_uncurry_iteratedDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ → F} {x : E} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x,t)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun q : E×ℝ => iteratedDeriv k (f q.1) q.2) (x,t) := by
  induction k with
  | zero =>
    apply hf.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun q => congrFun (iteratedDeriv_zero (f := f q.1)) q.2)
  | succ k ih =>
    have hcomp : ContDiffAt ℝ ∞
        (Function.uncurry (fun q : E×ℝ => fun s : ℝ => iteratedDeriv k (f q.1) s)) ((x,t),t) :=
      ih.comp ((x,t),t) ((contDiffAt_fst.fst).prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun q : E×ℝ => fderiv ℝ (iteratedDeriv k (f q.1)) q.2) (x,t) :=
      hcomp.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedDeriv_succ,deriv] using hd.clm_apply (contDiffAt_const (c := (1:ℝ)))

lemma contDiffAt_iteratedDeriv_parameter {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ → F} {x : E} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x,t)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun q : E => iteratedDeriv k (f q) t) x :=
  (contDiffAt_uncurry_iteratedDeriv hf k).comp x (contDiffAt_id.prodMk contDiffAt_const)

end WeakMTWTransport

end

end OAI

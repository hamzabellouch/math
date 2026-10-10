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

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fderiv_fst_eq_of_line_stationary {B : E×F → ℝ} {v a : E} {q : F}
    (hB : DifferentiableAt ℝ B (v,q))
    (hline : HasDerivAt (fun s : ℝ => B (v+s • a,q)) 0 0) :
    fderiv ℝ B (v,q) (a,0) = 0 := by
  have hp : HasDerivAt (fun s : ℝ => (v+s • a,q)) (a,0) 0 := by
    convert! (((hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const a)).prodMk
      (hasDerivAt_const (0:ℝ) q)) using 1; simp
  have hb : HasFDerivAt B (fderiv ℝ B (v,q)) (v+(0:ℝ) • a,q) := by simpa using hB.hasFDerivAt
  have h := hb.comp_hasDerivAt 0 hp
  exact h.unique hline

lemma fderiv_snd_eq_of_partial {B : E×F → ℝ} {v : E} {q : F} {D : F →L[ℝ] ℝ}
    (hB : DifferentiableAt ℝ B (v,q))
    (hpart : HasFDerivAt (fun y : F => B (v,y)) D q) (u : F) :
    fderiv ℝ B (v,q) (0,u) = D u := by
  have hp := (hasFDerivAt_const v q).prodMk (hasFDerivAt_id (𝕜 := ℝ) q)
  have h := hB.hasFDerivAt.comp q hp
  have heq := h.unique hpart
  exact congrArg (fun A : F →L[ℝ] ℝ => A u) heq

end WeakMTWTransport

end

end OAI

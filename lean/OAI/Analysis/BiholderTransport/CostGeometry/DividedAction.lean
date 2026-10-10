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
variable {M : Type*} [PseudoMetricSpace M]

lemma squared_dist_divided_action_le (x y z : M) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    dist x z^2/2 ≤ dist x y^2/(2*s) + dist y z^2/(2*(1-s)) := by
  have hns : 1-s ≠ 0 := (sub_pos.mpr hs1).ne'
  have htri := dist_triangle x y z
  have hab := dist_nonneg (x := x) (y := y)
  have hbc := dist_nonneg (x := y) (y := z)
  have hac := dist_nonneg (x := x) (y := z)
  have ht : dist x z^2 ≤ (dist x y+dist y z)^2 := by nlinarith
  have hc : (dist x y+dist y z)^2 ≤ dist x y^2/s + dist y z^2/(1-s) := by
    rw [div_add_div _ _ hs.ne' hns]
    apply (le_div_iff₀ (mul_pos hs (sub_pos.mpr hs1))).mpr
    nlinarith [sq_nonneg ((1-s)*dist x y-s*dist y z)]
  calc
    dist x z^2/2 ≤ (dist x y+dist y z)^2/2 := div_le_div_of_nonneg_right ht (by norm_num)
    _ ≤ (dist x y^2/s+dist y z^2/(1-s))/2 := div_le_div_of_nonneg_right hc (by norm_num)
    _ = _ := by field_simp [hs.ne',hns]

end WeakMTWTransport

end

end OAI

import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.MinimizingCorner

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem minimizing_vector_unique_of_injectivity {x : M} {v w : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (hw : w ∈ minimizingDomain x)
    (he : exp x v = exp x w) : v = w := by
  have hvm := injectivity_subset_minimizing x hv
  have hn : ‖w‖ = ‖v‖ := by
    change dist x (exp x v) = ‖v‖ at hvm
    change dist x (exp x w) = ‖w‖ at hw
    rw [← he] at hw
    exact hw.symm.trans hvm
  obtain ⟨a,ha,hae⟩ := hv
  let p : TangentBundle (model n) M := ⟨x,v⟩
  let q : TangentBundle (model n) M := ⟨x,w⟩
  have hjoin : geodesic q 1 = (geodesicFlow 1 p).1 := by
    change geodesic q 1 = geodesic p 1
    simpa only [exp_eq_geodesic] using he.symm
  have hend : geodesic (geodesicFlow 1 p) (a-1) = exp x (a • v) := by
    simp only [geodesic_shift,sub_add_cancel]
    exact (exp_mul_eq_geodesic p a).symm
  have hd : dist q.1 (geodesic (geodesicFlow 1 p) (a-1)) = ‖v‖ * (1+(a-1)) := by
    rw [hend]
    change dist x (exp x (a • v)) = _
    rw [hae]
    ring
  have hs := minimizing_broken_eq (p := q) (q := geodesicFlow 1 p) hn
    (geodesicFlow_norm 1 p) zero_lt_one (sub_pos.mpr ha) hjoin hd
  have hs' := congrArg (geodesicFlow (-1)) hs
  rw [← geodesicFlow_add,← geodesicFlow_add] at hs'
  simp only [neg_add_cancel,geodesicFlow_zero] at hs'
  have hh : HEq w v := (TotalSpace.ext_iff.mp hs').2
  exact (eq_of_heq hh).symm

 theorem exp_injOn_injectivity (x : M) : Set.InjOn (exp (n := n) x) (injectivityDomain x) := by
  intro v hv w hw he
  exact minimizing_vector_unique_of_injectivity hv (injectivity_subset_minimizing x hw) he
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

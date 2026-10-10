import Mathlib
import OAI.Geometry.WeakMTW.Variations.SegmentNonconjugacy

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

 theorem convexHull_nonconjugate (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) {A : Set (TangentSpace (model n) x)}
    (hA : ∀ a ∈ A, Nonconjugate x a)
    (hmin : convexHull ℝ A ⊆ minimizingDomain x) :
    ∀ v ∈ convexHull ℝ A, Nonconjugate x v := by
  let K := convexHull ℝ A ∩ {v | Nonconjugate x v}
  have hK : Convex ℝ K := by
    rw [convex_iff_segment_subset]
    intro u hu v hv w hw
    have hseg := (convex_convexHull ℝ A).segment_subset hu.1 hv.1
    exact ⟨hseg hw,segment_nonconjugacy hMTW x (hseg.trans hmin) hu.2 hv.2 w hw⟩
  have hAK : A ⊆ K := fun a ha => ⟨subset_convexHull ℝ A ha,hA a ha⟩
  exact fun v hv => (convexHull_min hAK hK hv).2

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

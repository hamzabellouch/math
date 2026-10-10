import Mathlib
import OAI.Geometry.WeakMTW.Support.FiniteActiveGraph
import OAI.Geometry.WeakMTW.Variations.HullNonconjugacy

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Pointwise
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem activeHull_critical_nonconjugate (hMTW : HasWeakMTW (n := n) (M := M))
    (y : ι → M) (h : ι → ℝ) {s : ℝ} (hs : 0 ≤ s) (hs₁ : s < 1)
    (hmin : ∀ p a, a ∈ activeHull (n := n) y h p → s•a ∈ minimizingDomain p)
    (p : M) {b : TangentSpace (model n) p} (hb : b ∈ activeHull y h p) :
    Nonconjugate p (s•b) := by
  apply convexHull_nonconjugate hMTW p (A := s • activeVelocities y h p)
  · rintro _ ⟨a,ha,rfl⟩
    exact nonconjugate_of_mem_injectivity p (strict_radial_mem_injectivity ha.1 hs hs₁)
  · rw [convexHull_smul]
    rintro _ ⟨a,ha,rfl⟩
    exact hmin p a ha
  · rw [convexHull_smul]
    exact ⟨b,hb,rfl⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

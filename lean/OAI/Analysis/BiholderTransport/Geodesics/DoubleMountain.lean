import Mathlib
import OAI.Analysis.BiholderTransport.Contact.GlobalSupport

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizingVector_active_twoMountain_left {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x} (hp₀ : p₀∈minimizingVectors x) :
    p₀∈activeLogs (cTransform (twoMountain x (riemannianExp x p₀) (riemannianExp x p₁))) x := by
  refine ⟨hp₀,?_⟩
  rw [contactGap,cTransform_cTransform_twoMountain,twoMountain_self,cTransform_twoMountain_left]
  ring

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizingVector_active_twoMountain_right {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x} (hp₁ : p₁∈minimizingVectors x) :
    p₁∈activeLogs (cTransform (twoMountain x (riemannianExp x p₀) (riemannianExp x p₁))) x := by
  refine ⟨hp₁,?_⟩
  rw [contactGap,cTransform_cTransform_twoMountain,twoMountain_self,cTransform_twoMountain_right]
  ring

lemma WeakMTW.double_mountain (hmtw : WeakMTW (n := n) (M := M)) {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x}
    (hp₀ : p₀∈minimizingVectors x) (hp₁ : p₁∈minimizingVectors x)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    a • p₀+b • p₁∈minimizingVectors x ∧ ∀ z : M,
      cost x (riemannianExp x (a • p₀+b • p₁))-cost z (riemannianExp x (a • p₀+b • p₁)) ≤
        max (cost x (riemannianExp x p₀)-cost z (riemannianExp x p₀))
          (cost x (riemannianExp x p₁)-cost z (riemannianExp x p₁)) := by
  let f := twoMountain x (riemannianExp x p₀) (riemannianExp x p₁)
  have hp : a • p₀+b • p₁∈convexHull ℝ (activeLogs (n := n) (cTransform f) x) :=
    (convex_convexHull _ _)
      (subset_convexHull _ _ (minimizingVector_active_twoMountain_left hp₀))
      (subset_convexHull _ _ (minimizingVector_active_twoMountain_right hp₁)) ha hb hab
  obtain ⟨hmin,hsup⟩ := hmtw.active_hull_global_support
    (continuous_cTransform (continuous_twoMountain x _ _)) hp
  refine ⟨hmin,?_⟩
  intro z
  have hh := hsup z
  rw [cTransform_cTransform_twoMountain,twoMountain_self] at hh
  change 0+cost x (riemannianExp x (a • p₀+b • p₁))≤
    twoMountain x (riemannianExp x p₀) (riemannianExp x p₁) z+
      cost z (riemannianExp x (a • p₀+b • p₁)) at hh
  exact sub_le_iff_le_add.mpr (by simpa only [zero_add,twoMountain] using hh)

lemma WeakMTW.convex_minimizingVectors (hmtw : WeakMTW (n := n) (M := M)) (x : M) :
    Convex ℝ (minimizingVectors (n := n) x) := by
  intro p hp q hq a b ha hb hab
  exact (hmtw.double_mountain hp hq ha hb hab).1
end WeakMTWTransport

end

end OAI

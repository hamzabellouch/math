import Mathlib
import OAI.Analysis.BiholderTransport.Duality.CompactDual
import OAI.Analysis.BiholderTransport.CostGeometry.ProjectionContinuation

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.global_support
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ normalSubdifferential (cTransform v) x) :
    p ∈ minimizingVectors x ∧ ∀ a : M,
      cTransform v x+cost x (riemannianExp x p) ≤
        cTransform v a+cost a (riemannianExp x p) := by
  let z : subgradientGraph (n := n) (cTransform v) := ⟨⟨x,p⟩,hp⟩
  have H := graph_global_min_at_left_limit (continuous_cTransform hv) (by norm_num : (0:ℝ)<1)
    (fun t ht => hmtw.injective_graphProjection hv ht.1 ht.2) z
  simpa only [one_smul,div_one,graphProjection,z] using H

lemma WeakMTW.active_hull_global_support
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    p ∈ minimizingVectors x ∧ ∀ a : M,
      cTransform v x+cost x (riemannianExp x p) ≤
        cTransform v a+cost a (riemannianExp x p) :=
  hmtw.global_support hv (active_hull_subset_normalSubdifferential hv x hp)

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def twoMountain (x y₀ y₁ z : M) : ℝ :=
  max (cost x y₀-cost z y₀) (cost x y₁-cost z y₁)

omit [CompactSpace M] [Nonempty M] in
lemma continuous_twoMountain (x y₀ y₁ : M) : Continuous (twoMountain x y₀ y₁) :=
  (continuous_const.sub (continuous_cost_left y₀)).max (continuous_const.sub (continuous_cost_left y₁))

omit [CompactSpace M] [Nonempty M] in
lemma twoMountain_self (x y₀ y₁ : M) : twoMountain x y₀ y₁ x=0 := by simp [twoMountain]

lemma cTransform_eq_of_lower_mountain {f : M → ℝ} (hf : Continuous f)
    {x y : M} (hx : f x=0) (hm : ∀ z, cost x y-cost z y≤f z) :
    cTransform f y = -cost x y := by
  apply le_antisymm
  · rw [cTransform_le_iff hf]
    intro z
    rw [cost_symm y z]
    linarith [hm z]
  · have hh := cTransform_gap_nonneg hf y x
    rw [contactGap,cost_symm y x,hx] at hh
    linarith

lemma cTransform_twoMountain_left (x y₀ y₁ : M) :
    cTransform (twoMountain x y₀ y₁) y₀ = -cost x y₀ :=
  cTransform_eq_of_lower_mountain (continuous_twoMountain x y₀ y₁)
    (twoMountain_self x y₀ y₁) (fun _ => le_max_left _ _)

lemma cTransform_twoMountain_right (x y₀ y₁ : M) :
    cTransform (twoMountain x y₀ y₁) y₁ = -cost x y₁ :=
  cTransform_eq_of_lower_mountain (continuous_twoMountain x y₀ y₁)
    (twoMountain_self x y₀ y₁) (fun _ => le_max_right _ _)

lemma cTransform_cTransform_twoMountain (x y₀ y₁ : M) :
    cTransform (cTransform (twoMountain x y₀ y₁))=twoMountain x y₀ y₁ := by
  funext z
  apply le_antisymm (cTransform_cTransform_le (continuous_twoMountain x y₀ y₁) z)
  apply max_le
  · have h := cTransform_gap_nonneg (continuous_cTransform (continuous_twoMountain x y₀ y₁)) z y₀
    rw [contactGap,cTransform_twoMountain_left] at h
    linarith
  · have h := cTransform_gap_nonneg (continuous_cTransform (continuous_twoMountain x y₀ y₁)) z y₁
    rw [contactGap,cTransform_twoMountain_right] at h
    linarith

end WeakMTWTransport

end

end OAI

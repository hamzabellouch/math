import OAI.Geometry.RCD.Metric.ConvexImageNoSupport
import Mathlib.Topology.Connected.Basic

namespace OAI

/-! # An interior isometry with no supporting boundary covers the ball -/

open Set Metric
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] [ProperSpace Y]

omit [ProperSpace Y] in
theorem metric_limit_closedBall_image {n : ℕ} (F : Y → Euclidean n) (q : Y)
    (hcompact : IsCompact (F '' closedBall q (1/256)))
    (hconv : Convex ℝ (F '' closedBall q (1/256)))
    (hiso : ∀ y z, dist y q<1/16 → dist z q<1/16 → dist (F y) (F z)=dist y z)
    (hno : ∀ y, dist y q<1/256 → ∀ a : Euclidean n, ‖a‖=1 →
      (∀ z∈closedBall q (1/256), ⟪F z-F y,a⟫_ℝ≤0) → False) :
    F '' closedBall q (1/256)=closedBall (F q) (1/256) := by
  let C := F '' closedBall q (1/256)
  have hq : q∈closedBall q (1/256:ℝ) := by simp
  have hinner : (interior C).Nonempty := convex_image_interior_of_no_support F _ hconv hq
    (hno q (by simp))
  have hint (y : Y) (hy : dist y q<1/256) : F y∈interior C := by
    by_contra hnot
    obtain ⟨a,ha,hs⟩ := convex_unit_support C hconv hinner hnot
    exact hno y hy a ha (fun z hz => hs (F z) ⟨z,hz,rfl⟩)
  have hd (y : Y) (hy : dist y q≤1/256) : dist (F y) (F q)=dist y q :=
    hiso y q (hy.trans_lt (by norm_num)) (by simp)
  have hball : ball (F q) (1/256)⊆C := by
    have hcover : ball (F q) (1/256)⊆interior C∪Cᶜ := by
      intro z hz
      by_cases hzc : z∈C
      · obtain ⟨y,hy,rfl⟩ := hzc
        exact Or.inl (hint y (by
          change dist (F y) (F q)<1/256 at hz
          rwa [hd y hy] at hz))
      · exact Or.inr hzc
    have hi : ball (F q) (1/256)⊆interior C :=
      (convex_ball (F q) (1/256:ℝ)).isPreconnected.subset_left_of_subset_union
        isOpen_interior hcompact.isClosed.isOpen_compl
        (disjoint_compl_right.mono_left interior_subset) hcover
        ⟨F q,by simp,hint q (by simp)⟩
    exact hi.trans interior_subset
  apply subset_antisymm
  · rintro _ ⟨y,hy,rfl⟩
    exact (hd y hy).le.trans hy
  · rw [← closure_ball (F q) (by norm_num : (1/256:ℝ)≠0)]
    exact closure_minimal hball hcompact.isClosed

end RegularPointCoordinates

end

end OAI

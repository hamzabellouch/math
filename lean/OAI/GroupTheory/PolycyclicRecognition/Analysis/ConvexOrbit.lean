import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineLabels
import Mathlib.Analysis.Convex.Strict.Extreme

namespace OAI

/-! # From convex orbit constraints to a single linear label -/

namespace PolycyclicRecognition

universe u v

/-- Strict convexity prevents a convex combination of points in a closed ball
from lying on the sphere unless it is one of the original points. This is
the finite-orbit selection step of the profile affinity argument. -/
theorem mem_of_mem_convexHull_of_norm_eq
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [StrictConvexSpace ℝ W]
    {s : Set W} {x : W} {r : ℝ}
    (hs : ∀ y ∈ s, ‖y‖ ≤ r) (hx : x ∈ convexHull ℝ s) (hnorm : ‖x‖ = r) :
    x ∈ s := by
  by_cases hr : r = 0
  · have hs0 : s ⊆ {0} := by
      intro y hy
      exact norm_eq_zero.mp (le_antisymm ((hs y hy).trans_eq hr) (norm_nonneg y))
    have heq : convexHull ℝ s = s := by
      exact (Set.subsingleton_singleton.anti hs0).convex.convexHull_eq
    rwa [heq] at hx
  · have hball : convexHull ℝ s ⊆ Metric.closedBall (0 : W) r := by
      apply convexHull_min _ (convex_closedBall 0 r)
      intro y hy
      simpa only [Metric.mem_closedBall, dist_zero_right] using hs y hy
    have hsphere : x ∈ Metric.sphere (0 : W) r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hnorm
    have hext := StrictConvexSpace.sphere_subset_extremePoints_closedBall (0 : W) hr hsphere
    exact extremePoints_convexHull_subset
      (inter_extremePoints_subset_extremePoints_of_subset hball ⟨hx, hext⟩)

/-- A linear map lying pointwise in a finite orbit convex hull is one of the
orbit maps if all these vectors have the same strictly convex norm. -/
theorem exists_eq_of_convex_orbit
    {ι : Type u} [Finite ι] {W : Type v}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [StrictConvexSpace ℝ W]
    (B : W →ₗ[ℝ] W) (A : ι → W →ₗ[ℝ] W)
    (hconv : ∀ w, B w ∈ convexHull ℝ (Set.range fun i => A i w))
    (hnorm : ∀ w i, ‖A i w‖ = ‖B w‖) : ∃ i, B = A i := by
  apply exists_eq_of_pointwise_linear_selection B A
  intro w
  obtain ⟨i, hi⟩ := mem_of_mem_convexHull_of_norm_eq
    (s := Set.range fun i => A i w)
    (by rintro y ⟨i, rfl⟩; exact (hnorm w i).le) (hconv w) rfl
  exact ⟨i, hi.symm⟩


end PolycyclicRecognition

end OAI

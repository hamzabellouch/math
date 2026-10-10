import OAI.Geometry.RCD.Coordinates.IterationLimit

namespace OAI

/-!
# Pair segments from harmonic-coordinate ellipsoids

The final analytic argument only needs a coordinate segment to stay in the
larger working region, with comparable frozen metrics along it. Central
ellipsoid containment and the nearby-center comparison imply precisely
those facts. The source of the final chart may be a smaller open subset.
-/

open Set

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_frozen_sub_le_of_mem_segment (T : E →L[ℝ] E)
    {A B P : E} (hP : P ∈ segment ℝ A B) :
    ‖T (P - A)‖ ≤ ‖T (B - A)‖ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hP
  have haeq : a = 1 - b := by linarith
  have hbeq : (a • A + b • B) - A = b • (B - A) := by
    rw [haeq]
    module
  rw [hbeq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- Every point of the short coordinate segment has a preimage in the
nearby metric ball. Thus the nearby-center bound applies along the
whole segment, without any differentiability of the frozen metrics. -/
theorem segment_geometry_of_ellipsoid
    {X : Type*} [MetricSpace X] (u : X → E) (frozen : E → E ≃L[ℝ] E)
    {Ω : Set E} {W : Set X} {x z : X} {r c G : ℝ}
    (hend : ‖frozen (u x) (u z - u x)‖ < c * r)
    (hball : ∀ P : E, ‖frozen (u x) (P - u x)‖ < c * r →
      P ∈ Ω ∧ ∃ y ∈ W, dist x y < r ∧ u y = P)
    (hnear : ∀ y ∈ W, dist x y < r → ∀ w : E,
      ‖frozen (u y) w‖ ≤ G * ‖frozen (u x) w‖) :
    segment ℝ (u x) (u z) ⊆ Ω ∧ ∀ P ∈ segment ℝ (u x) (u z),
      ‖frozen P (u z - u x)‖ ≤ G * ‖frozen (u x) (u z - u x)‖ := by
  have hinside (P : E) (hP : P ∈ segment ℝ (u x) (u z)) :
      P ∈ Ω ∧ ∃ y ∈ W, dist x y < r ∧ u y = P := by
    apply hball P
    exact (norm_frozen_sub_le_of_mem_segment (frozen (u x)).toContinuousLinearMap hP).trans_lt hend
  constructor
  · intro P hP
    exact (hinside P hP).1
  · intro P hP
    obtain ⟨y, hy, hdist, rfl⟩ := (hinside P hP).2
    exact hnear y hy hdist _

/-- All ingredients of the final pair geometry follow from endpoint
separation, ellipsoid containment, nearby metric comparison, and a
diameter bound on the small source domain. -/
theorem iterationPairGeometry_of_ellipsoids
    {X : Type*} [MetricSpace X] (u : X → E) (D W : Set X)
    (Ω : Set E) (frozen : ℕ → E → E ≃L[ℝ] E)
    {r0 T B G c : ℝ} (hr0 : 0 < r0) (hT : 1 ≤ T) (hB : 1 ≤ B) (hG : 1 ≤ G)
    (hc : 0 < c) (hmargin : G < c * iterationPairMultiplier T B G)
    (hdiam : ∀ x ∈ D, ∀ z ∈ D, iterationPairMultiplier T B G * dist x z ≤ r0)
    (hend : ∀ i x, x ∈ D → ∀ z, z ∈ D → x ≠ z →
      iterationPairMultiplier T B G * dist x z ≤ iterationRadius r0 i →
      iterationRadius r0 i ≤ 2 * iterationPairMultiplier T B G * dist x z →
      G⁻¹ * dist x z ≤ ‖frozen i (u x) (u z - u x)‖ ∧
      ‖frozen i (u x) (u z - u x)‖ ≤ G * dist x z)
    (hball : ∀ i x, x ∈ D → ∀ P : E,
      ‖frozen i (u x) (P - u x)‖ < c * iterationRadius r0 i →
      P ∈ Ω ∧ ∃ y ∈ W, dist x y < iterationRadius r0 i ∧ u y = P)
    (hnear : ∀ i x, x ∈ D → ∀ y, y ∈ W → dist x y < iterationRadius r0 i →
      ∀ w : E, ‖frozen i (u y) w‖ ≤ G * ‖frozen i (u x) w‖) :
    IterationPairGeometry (fun x : D => u x) Ω frozen r0 T B G := by
  apply iterationPairGeometry_of_all_scales (X := D) (fun x => u x) Ω frozen hr0 hT hB hG
    (fun x z => hdiam x x.property z z.property)
  intro i x z hxz hscale hscale'
  have hxz' : (x : X) ≠ z := fun h => hxz (Subtype.ext h)
  obtain ⟨hl, hu⟩ := hend i x x.property z z.property hxz' hscale hscale'
  refine ⟨hl, hu, ?_⟩
  apply segment_geometry_of_ellipsoid u (frozen i) (x := x) (z := z)
  · calc
      ‖frozen i (u x) (u z - u x)‖ ≤ G * dist (x : X) z := hu
      _ < (c * iterationPairMultiplier T B G) * dist (x : X) z :=
        mul_lt_mul_of_pos_right hmargin (dist_pos.mpr hxz')
      _ = c * (iterationPairMultiplier T B G * dist (x : X) z) := by ring
      _ ≤ c * iterationRadius r0 i := mul_le_mul_of_nonneg_left hscale hc.le
  · exact hball i x x.property
  · exact hnear i x x.property

end RegularPointCoordinates

end OAI

import OAI.Geometry.TriangularCovering.TriangleArea

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def projLinear (u : Space) : Space →ₗ[ℝ] Space :=
  LinearMap.id - (innerₛₗ ℝ u).smulRight u

@[simp] lemma projLinear_apply (u z : Space) : projLinear u z = projection u z := rfl

lemma projection_perp {u : Space} (hu : ‖u‖ = 1) (z : Space) :
    inner ℝ u (projection u z) = 0 := by
  simp [projection, inner_sub_right, inner_smul_right, hu]

lemma projection_inner {u : Space} (hu : ‖u‖ = 1) (b c : Space) :
    inner ℝ (projection u b) (projection u c) =
      inner ℝ b c - inner ℝ u b * inner ℝ u c := by
  simp only [projection, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_trivial, real_inner_self_eq_norm_sq, hu]
  rw [real_inner_comm b u]
  ring

def cross3 (b c : Space) : Space := WithLp.toLp 2 (crossProduct b.ofLp c.ofLp)

lemma inner_coord (a b : Space) :
    inner ℝ a b = a 0*b 0 + a 1*b 1 + a 2*b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

lemma cross3_coord (b c : Space) :
    cross3 b c = !₂[b 1*c 2-b 2*c 1, b 2*c 0-b 0*c 2, b 0*c 1-b 1*c 0] := rfl

lemma triple_gram_identity (u b c : Space) :
    (inner ℝ u (cross3 b c))^2 =
      inner ℝ u u * (inner ℝ b b * inner ℝ c c - (inner ℝ b c)^2) -
      inner ℝ b b * (inner ℝ u c)^2 - inner ℝ c c * (inner ℝ u b)^2 +
      2 * inner ℝ b c * inner ℝ u b * inner ℝ u c := by
  simp only [inner_coord, cross3_coord]
  dsimp
  ring

lemma projected_gram {u : Space} (hu : ‖u‖ = 1) (b c : Space) :
    inner ℝ (projection u b) (projection u b) * inner ℝ (projection u c) (projection u c) -
      (inner ℝ (projection u b) (projection u c))^2 = (inner ℝ u (cross3 b c))^2 := by
  rw [projection_inner hu, projection_inner hu, projection_inner hu, triple_gram_identity,
    real_inner_self_eq_norm_sq u, hu]
  ring

lemma projection_triangle_measure {u : Space} (hu : ‖u‖ = 1) (a b c : Space) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' triangle a b c) =
      ENNReal.ofReal (|inner ℝ u (cross3 (b-a) (c-a))|/2) := by
  change Measure.euclideanHausdorffMeasure 2 (projLinear u '' triangle a b c) = _
  rw [triangle_image_linear]
  have hun : u ≠ 0 := by intro h; simp [h] at hu
  have hp := perpendicular_triangle_measure (E := Space) (by simp) u
    (projection u a) (projection u b) (projection u c) hun
    (projection_perp hu a) (projection_perp hu b) (projection_perp hu c)
  change Measure.euclideanHausdorffMeasure 2
    (triangle (projection u a) (projection u b) (projection u c)) = _
  rw [hp]
  have hab : projection u b - projection u a = projection u (b-a) :=
    ((projLinear u).map_sub b a).symm
  have hac : projection u c - projection u a = projection u (c-a) :=
    ((projLinear u).map_sub c a).symm
  rw [hab, hac, projected_gram hu, Real.sqrt_sq_eq_abs]

lemma cross3_gram (b c : Space) :
    inner ℝ (cross3 b c) (cross3 b c) =
      inner ℝ b b * inner ℝ c c - (inner ℝ b c)^2 := by
  simp only [inner_coord, cross3_coord]
  dsimp
  ring

lemma affineIndependent_of_cross3_ne_zero (a b c : Space)
    (h : cross3 (b-a) (c-a) ≠ 0) : AffineIndependent ℝ (![a,b,c] : Fin 3 → Space) := by
  have hpi : crossProduct (b-a).ofLp (c-a).ofLp ≠ 0 := by
    intro hz
    apply h
    unfold cross3
    rw [hz]
    rfl
  have hl := crossProduct_ne_zero_iff_linearIndependent.mp hpi
  have hlE : LinearIndependent ℝ (![b-a,c-a] : Fin 2 → Space) := by
    apply LinearIndependent.of_comp (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap
    convert hl using 1
    funext i
    fin_cases i <;> rfl
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0,
    ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
  convert hlE using 1; try rfl
  ext i
  fin_cases i <;> rfl

lemma projected_affineIndependent {u : Space} (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) :
    AffineIndependent ℝ (![projection u a, projection u b, projection u c] : Fin 3 → Space) := by
  apply affineIndependent_of_cross3_ne_zero
  have hab : projection u b - projection u a = projection u (b-a) :=
    ((projLinear u).map_sub b a).symm
  have hac : projection u c - projection u a = projection u (c-a) :=
    ((projLinear u).map_sub c a).symm
  rw [hab, hac]
  intro hz
  have hh := cross3_gram (projection u (b-a)) (projection u (c-a))
  rw [hz, inner_zero_left, projected_gram hu] at hh
  exact h (sq_eq_zero_iff.mp hh.symm)

lemma triangle_compact (a b c : Space) : IsCompact (triangle a b c) :=
  (finite_range (![a,b,c] : Fin 3 → Space)).isCompact_convexHull ℝ

def projectedCylinder (u : Space) (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) : TriCylinder where
  axis := u
  base := projection u '' triangle a b c
  unit_axis := hu
  perpendicular := by
    rintro _ ⟨z, _, rfl⟩
    exact projection_perp hu z
  triangular := by
    refine ⟨![projection u a, projection u b, projection u c],
      projected_affineIndependent hu a b c h, ?_⟩
    exact triangle_image_linear (projLinear u) a b c
  compact := (triangle_compact a b c).image (projLinear u).continuous_of_finiteDimensional
  convex := (convex_convexHull ℝ _).linear_image (projLinear u)
  measurable := ((triangle_compact a b c).image
    (projLinear u).continuous_of_finiteDimensional).measurableSet
  finite_area := by rw [projection_triangle_measure hu]; exact ENNReal.ofReal_ne_top

lemma projectedCylinder_area (u : Space) (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) :
    area (projectedCylinder u hu a b c h).base = |inner ℝ u (cross3 (b-a) (c-a))|/2 := by
  unfold area
  rw [projectedCylinder, projection_triangle_measure hu, ENNReal.toReal_ofReal (by positivity)]

lemma projectedCylinder_mem (u : Space) (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) {p z : Space} (hp : p ∈ triangle a b c)
    (r : ℝ) (hz : z = p + r • u) : z ∈ (projectedCylinder u hu a b c h).carrier := by
  refine ⟨projection u p, ⟨p, hp, rfl⟩, r + inner ℝ u p, ?_⟩
  change z = projection u p + (r + inner ℝ u p) • u
  rw [hz, projection]
  module

def unit (v : Space) : Space := ‖v‖⁻¹ • v

lemma unit_norm {v : Space} (hv : v ≠ 0) : ‖unit v‖ = 1 := by
  simp [unit, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma unit_mul_norm (v : Space) : ‖v‖ • unit v = v := by
  by_cases hv : v = 0
  · simp [unit, hv]
  · simp [unit, smul_smul, norm_ne_zero_iff.mpr hv]

lemma projectedCylinder_mem_direction (v : Space) (hv : v ≠ 0) (a b c : Space)
    (h : inner ℝ (unit v) (cross3 (b-a) (c-a)) ≠ 0) {p z : Space}
    (hp : p ∈ triangle a b c) (r : ℝ) (hz : z = p + r • v) :
    z ∈ (projectedCylinder (unit v) (unit_norm hv) a b c h).carrier := by
  apply projectedCylinder_mem (unit v) (unit_norm hv) a b c h hp (r * ‖v‖)
  rw [mul_smul, unit_mul_norm, hz]

end TriangularCovering

end

end OAI

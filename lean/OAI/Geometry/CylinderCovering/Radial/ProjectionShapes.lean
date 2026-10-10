import OAI.Geometry.CylinderCovering.Radial.Projection

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace

namespace RadialProjection
open TriangularCovering

theorem transverse_projection_eq_zero_iff {e w z : Space}
    (he : ‖e‖ = 1) (hw : inner ℝ e w = 0) (hz : inner ℝ e z = 0) :
    projection (unit (e + w)) z = 0 ↔ z = 0 := by
  have hnorm : ‖e + w‖ ≠ 0 := norm_ne_zero_iff.mpr (sideways_ne_zero he hw)
  have hinner : inner ℝ e (unit (e + w)) = ‖e + w‖⁻¹ := by
    simp [TriangularCovering.unit, inner_smul_right, inner_add_right,
      he, hw]
  constructor
  · intro hp
    have heq : z = (inner ℝ (unit (e + w)) z) • unit (e + w) :=
      sub_eq_zero.mp hp
    have hmul := congrArg (fun v : Space => inner ℝ e v) heq
    rw [hz, inner_smul_right, hinner] at hmul
    have hc : inner ℝ (unit (e + w)) z = 0 :=
      (mul_eq_zero.mp hmul.symm).resolve_right (inv_ne_zero hnorm)
    simpa only [hc, zero_smul] using heq
  · rintro rfl
    simp [projection]

def projectedCoordinateAffine (u p₀ a b : Space) : (ℝ × ℝ) →ᵃ[ℝ] Space :=
  (projLinear u).toAffineMap.comp (coordinateAffine p₀ a b)

@[simp] theorem projectedCoordinateAffine_apply (u p₀ a b : Space) (p : ℝ × ℝ) :
    projectedCoordinateAffine u p₀ a b p =
      projection u (p₀ + p.1 • a + p.2 • b) := rfl

theorem coordinateAffine_injective (p₀ : Space) {a b : Space}
    (hab : LinearIndependent ℝ (![a,b] : Fin 2 → Space)) :
    Function.Injective (coordinateAffine p₀ a b) := by
  intro p q hpq
  have hsum : p.1 • a + p.2 • b = q.1 • a + q.2 • b := by
    change p₀ + p.1 • a + p.2 • b = p₀ + q.1 • a + q.2 • b at hpq
    exact add_left_cancel (by simpa only [add_assoc] using hpq)
  have hcoords : (![p.1,p.2] : Fin 2 → ℝ) = ![q.1,q.2] :=
    hab.fintypeLinearCombination_injective (by
      simpa [Fintype.linearCombination_apply, Fin.sum_univ_succ] using hsum)
  exact Prod.ext (congrFun hcoords 0) (congrFun hcoords 1)

theorem projectedCoordinateAffine_injective (p₀ : Space) {e w a b : Space}
    (he : ‖e‖ = 1) (hw : inner ℝ e w = 0)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hab : LinearIndependent ℝ (![a,b] : Fin 2 → Space)) :
    Function.Injective (projectedCoordinateAffine (unit (e + w)) p₀ a b) := by
  intro p q hpq
  apply coordinateAffine_injective p₀ hab
  apply sub_eq_zero.mp
  apply (transverse_projection_eq_zero_iff he hw ?_).mp
  · change projLinear (unit (e + w))
        (coordinateAffine p₀ a b p - coordinateAffine p₀ a b q) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hpq
  · change inner ℝ e
      ((p₀ + p.1 • a + p.2 • b) - (p₀ + q.1 • a + q.2 • b)) = 0
    simp only [inner_sub_right, inner_add_right, inner_smul_right, ha, hb,
      mul_zero, add_zero, sub_self]

theorem projectedCoordinateAffine_convex_iff (p₀ : Space) {e w a b : Space}
    (he : ‖e‖ = 1) (hw : inner ℝ e w = 0)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hab : LinearIndependent ℝ (![a,b] : Fin 2 → Space)) (S : Set (ℝ × ℝ)) :
    Convex ℝ (projectedCoordinateAffine (unit (e + w)) p₀ a b '' S) ↔ Convex ℝ S := by
  constructor
  · intro h
    have hpre := h.affine_preimage (projectedCoordinateAffine (unit (e + w)) p₀ a b)
    rwa [Set.preimage_image_eq _
      (projectedCoordinateAffine_injective p₀ he hw ha hb hab)] at hpre
  · exact fun h => h.affine_image _

theorem projectedCoordinateAffine_affineIndependent_iff
    (p₀ : Space) {e w a b : Space}
    (he : ‖e‖ = 1) (hw : inner ℝ e w = 0)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hab : LinearIndependent ℝ (![a,b] : Fin 2 → Space))
    {ι : Type*} (p : ι → ℝ × ℝ) :
    AffineIndependent ℝ (projectedCoordinateAffine (unit (e + w)) p₀ a b ∘ p) ↔
      AffineIndependent ℝ p :=
  (projectedCoordinateAffine (unit (e + w)) p₀ a b).affineIndependent_iff
    (projectedCoordinateAffine_injective p₀ he hw ha hb hab)

theorem projectedCoordinateAffine_convexHull (u p₀ a b : Space) (S : Set (ℝ × ℝ)) :
    projectedCoordinateAffine u p₀ a b '' convexHull ℝ S =
      convexHull ℝ (projectedCoordinateAffine u p₀ a b '' S) :=
  (projectedCoordinateAffine u p₀ a b).image_convexHull S

end RadialProjection

end

end OAI

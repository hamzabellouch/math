import OAI.Geometry.CylinderCovering.Footprints.FootprintsDefinitions
import OAI.Geometry.CylinderCovering.Footprints.Shapes
import OAI.Geometry.CylinderCovering.Radial.ProjectionShapes

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace

namespace RadialFootprints

def halfheightVertices (ρ e M m : ℝ) : Fin 4 → ℝ × ℝ :=
  ![(-e, -m*e-ρ*e), (-e, -m*e+ρ*e),
    (M+e, m*(M+e)-ρ*(M+3*e)), (M+e, m*(M+e)+ρ*(M+3*e))]

theorem halfheightFootprint_eq_affine {ρ : ℝ} (hρ : ρ ≠ 0) (e M m : ℝ) :
    halfheightFootprint ρ e M m =
      CylinderCovering.Footprints.affineFootprint m M (2*ρ) (e/(2*ρ)) (e/(2*ρ)) := by
  have hleft : -(e/(2*ρ))*(2*ρ) = -e := by field_simp
  have hright : M+(e/(2*ρ))*(2*ρ) = M+e := by field_simp
  have hwidth (w : ℝ) : (2*ρ)/2*w+(e/(2*ρ))*(2*ρ)^2 = ρ*(w+2*e) := by
    field_simp
  ext p
  simp only [halfheightFootprint, CylinderCovering.Footprints.affineFootprint,
    mem_ofPred_eq, mem_Icc, hleft, hright, hwidth, and_assoc]

theorem halfheightVertices_eq_trapezoid {ρ : ℝ} (hρ : ρ ≠ 0) (e M m : ℝ) :
    halfheightVertices ρ e M m =
      CylinderCovering.Footprints.trapezoidVertices m M (2*ρ) (e/(2*ρ)) (e/(2*ρ)) := by
  funext i
  fin_cases i <;> apply Prod.ext <;>
    simp [halfheightVertices, CylinderCovering.Footprints.trapezoidVertices] <;>
    field_simp <;> ring

theorem halfheightFootprint_eq_convexHull {ρ e M : ℝ} (m : ℝ)
    (hρ : 0 < ρ) (he : 0 < e) (hM : 0 ≤ M) :
    halfheightFootprint ρ e M m =
      convexHull ℝ (range (halfheightVertices ρ e M m)) := by
  have hA : 0 < e/(2*ρ) := by positivity
  have hlen : 0 < M+2*(e/(2*ρ))*(2*ρ) := by
    have heq : M+2*(e/(2*ρ))*(2*ρ) = M+2*e := by field_simp
    rw [heq]
    positivity
  rw [halfheightFootprint_eq_affine hρ.ne', halfheightVertices_eq_trapezoid hρ.ne']
  exact CylinderCovering.Footprints.affineFootprint_eq_convexHull_trapezoid
    (by positivity) (by linarith) hlen

theorem halfheightVertices_injective {ρ e M : ℝ} (m : ℝ)
    (hρ : 0 < ρ) (he : 0 < e) (hM : 0 ≤ M) :
    Function.Injective (halfheightVertices ρ e M m) := by
  have hA : 0 < e/(2*ρ) := by positivity
  have hlen : 0 < M+2*(e/(2*ρ))*(2*ρ) := by
    have heq : M+2*(e/(2*ρ))*(2*ρ) = M+2*e := by field_simp
    rw [heq]
    positivity
  rw [halfheightVertices_eq_trapezoid hρ.ne']
  exact CylinderCovering.Footprints.trapezoidVertices_injective
    (by positivity) (by linarith) hlen

theorem halfheightFootprint_convex {ρ e M : ℝ} (m : ℝ)
    (hρ : 0 < ρ) (he : 0 < e) (hM : 0 ≤ M) :
    Convex ℝ (halfheightFootprint ρ e M m) := by
  rw [halfheightFootprint_eq_convexHull m hρ he hM]
  exact convex_convexHull ℝ _

theorem halfheightFootprint_isCompact (ρ e M m : ℝ) :
    IsCompact (halfheightFootprint ρ e M m) := by
  have hset : halfheightFootprint ρ e M m =
      {p : ℝ × ℝ | p.1 ∈ Icc (-e) (M+e) ∧
        p.2 ∈ Icc (m*p.1-ρ*(p.1+2*e)) (m*p.1+ρ*(p.1+2*e))} := by
    ext p
    simp only [halfheightFootprint, mem_ofPred_eq, mem_Icc, abs_le]
    constructor <;> rintro ⟨hp,hleft,hright⟩ <;>
      exact ⟨hp, by linarith, by linarith⟩
  rw [hset]
  exact CylinderCovering.Footprints.isCompact_closedBand
    (f := fun w => m*w-ρ*(w+2*e)) (g := fun w => m*w+ρ*(w+2*e))
    (by fun_prop) (by fun_prop) _ _

theorem halfheight_parallel_sides (ρ e M m : ℝ) :
    halfheightVertices ρ e M m 1 - halfheightVertices ρ e M m 0 = (0,2*ρ*e) ∧
    halfheightVertices ρ e M m 3 - halfheightVertices ρ e M m 2 =
      (0,2*ρ*(M+3*e)) := by
  constructor <;> ext <;> simp [halfheightVertices] <;> ring

theorem projected_halfheight_trapezoid (p₀ : TriangularCovering.Space)
    {axis tilt a b : TriangularCovering.Space} {ρ e M : ℝ} (m : ℝ)
    (haxis : ‖axis‖ = 1) (htilt : inner ℝ axis tilt = 0)
    (ha : inner ℝ axis a = 0) (hb : inner ℝ axis b = 0)
    (hab : LinearIndependent ℝ (![a,b] : Fin 2 → TriangularCovering.Space))
    (hρ : 0 < ρ) (he : 0 < e) (hM : 0 ≤ M) :
    let f := RadialProjection.projectedCoordinateAffine
      (TriangularCovering.unit (axis+tilt)) p₀ a b
    f '' halfheightFootprint ρ e M m =
      convexHull ℝ (range (f ∘ halfheightVertices ρ e M m)) ∧
    Function.Injective (f ∘ halfheightVertices ρ e M m) := by
  dsimp only
  constructor
  · rw [halfheightFootprint_eq_convexHull m hρ he hM,
      RadialProjection.projectedCoordinateAffine_convexHull, ← range_comp]
  · exact (RadialProjection.projectedCoordinateAffine_injective p₀ haxis htilt ha hb hab).comp
      (halfheightVertices_injective m hρ he hM)

end RadialFootprints

end

end OAI

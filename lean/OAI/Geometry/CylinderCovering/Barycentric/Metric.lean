import OAI.Geometry.CylinderCovering.Barycentric.MetricDefinitions
import OAI.Geometry.CylinderCovering.Convexity.NormalFrameProjection

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace Pointwise
namespace CylinderBarycentricMetric

private theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
private theorem sqrt_two_ne : Real.sqrt 2 ≠ 0 := sqrt_two_pos.ne'

theorem embedding_sum (z : Physical) : ∑ i : Fin 4, embedding z i = 0 := by
  simp [embedding, Fin.sum_univ_succ]
  ring

theorem embedding_norm (z : Physical) : ‖embedding z‖ = ‖z‖ := by
  have hs : ‖embedding z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, Fin.sum_univ_three]
    simp only [embedding, LinearMap.coe_mk, AddHom.coe_mk]
    dsimp
    field_simp
    nlinarith [sqrt_two_sq]
  nlinarith [norm_nonneg (embedding z), norm_nonneg z]

def embeddingIsometry : Physical →ₗᵢ[ℝ] Barycentric :=
  { embedding with norm_map' := embedding_norm }

theorem inverse_embedding (z : Physical) : inverse (embedding z) = z := by
  ext i
  fin_cases i <;> simp [inverse, embedding] <;> field_simp <;>
    norm_num [sqrt_two_sq]
  linarith

theorem embedding_inverse (p : Barycentric) (hp : ∑ i : Fin 4, p i = 0) :
    embedding (inverse p) = p := by
  simp only [Fin.sum_univ_four] at hp
  ext i
  fin_cases i <;> simp [inverse, embedding] <;> field_simp <;>
    norm_num [sqrt_two_sq] <;> linarith

theorem inverse_norm (p : Barycentric) (hp : ∑ i : Fin 4, p i = 0) :
    ‖inverse p‖ = ‖p‖ := by
  rw [← embedding_norm, embedding_inverse p hp]

theorem fromPhysical_point (x y t : ℝ) :
    fromPhysical (TriangularCovering.point x y t) =
      !₂[(1-t+x)/2, (1-t-x)/2, (t+y)/2, (t-y)/2] := by
  ext i
  fin_cases i <;>
    simp [fromPhysical, offset, embedding, TriangularCovering.point, TriangularCovering.H] <;>
    field_simp <;> norm_num [sqrt_two_sq] <;> ring

theorem fromPhysical_image : fromPhysical '' TriangularCovering.K = tetrahedron := by
  ext p
  constructor
  · rintro ⟨z, ⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,rfl⟩
    rw [fromPhysical_point]
    constructor
    · intro i
      fin_cases i <;> dsimp <;> linarith [(abs_le.mp hx).1, (abs_le.mp hx).2,
        (abs_le.mp hy).1, (abs_le.mp hy).2]
    · simp [Fin.sum_univ_succ]
      ring
  · rintro ⟨hp,hs⟩
    simp only [Fin.sum_univ_four] at hs
    refine ⟨TriangularCovering.point (p 0-p 1) (p 2-p 3) (p 2+p 3), ?_, ?_⟩
    · refine ⟨p 0-p 1,p 2-p 3,p 2+p 3,?_,?_,?_,?_,rfl⟩
      · linarith [hp 2,hp 3]
      · linarith [hp 0,hp 1]
      · rw [abs_le]
        constructor <;> linarith [hp 0,hp 1]
      · rw [abs_le]
        constructor <;> linarith [hp 2,hp 3]
    · rw [fromPhysical_point]
      ext i
      fin_cases i <;> dsimp <;> linarith

theorem embedding_inner (v z : Physical) :
    inner ℝ (embedding v) (embedding z) = inner ℝ v z :=
  embeddingIsometry.inner_map_map v z

theorem embedding_projection (v z : Physical) :
    embedding (TriangularCovering.projection v z) = projection (embedding v) (embedding z) := by
  simp [TriangularCovering.projection, projection, embedding_inner]

theorem projection_add (u p q : Barycentric) :
    projection u (p+q) = projection u p + projection u q := by
  simp only [projection, inner_add_right, add_smul]
  module

theorem projection_smul (u p : Barycentric) (r : ℝ) :
    projection u (r • p) = r • projection u p := by
  simp only [projection, inner_smul_right, smul_sub, smul_smul]

theorem projection_fromPhysical (v z : Physical) :
    projection (embedding v) (fromPhysical z) =
      projection (embedding v) offset + embedding ((1 / Real.sqrt 2) •
        TriangularCovering.projection v z) := by
  rw [fromPhysical, projection_add, projection_smul, ← embedding_projection, map_smul]

theorem shadow_image (v : Physical) :
    projection (embedding v) '' tetrahedron =
      (fun z : Physical => projection (embedding v) offset + embedding z) ''
        ((1 / Real.sqrt 2 : ℝ) • (TriangularCovering.projection v '' TriangularCovering.K)) := by
  rw [← fromPhysical_image, Set.image_image, ← Set.image_smul, Set.image_image,
    Set.image_image]
  apply Set.image_congr
  intro z hz
  exact projection_fromPhysical v z

theorem shadowArea_embedding (v : Physical) :
    shadowArea (embedding v) = (1 / 2 : ℝ) * TriangularCovering.shadowArea v := by
  unfold shadowArea
  rw [shadow_image]
  have hi : Isometry (fun z : Physical => projection (embedding v) offset + embedding z) :=
    (isometry_add_left _).comp embeddingIsometry.isometry
  rw [hi.euclideanHausdorffMeasure_image,
    Measure.euclideanHausdorffMeasure_smul₀ 2 (one_div_ne_zero sqrt_two_ne),
    ENNReal.toReal_smul]
  simp only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
    abs_div, abs_one, abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ)), div_pow, sqrt_two_sq,
    one_pow, smul_eq_mul]
  rfl

theorem physical_shadow_eq_abs_embedding (v : Physical) (hv : ‖v‖ = 1) :
    TriangularCovering.shadowArea v = ∑ i : Fin 4, |embedding v i| := by
  have h0 : inner ℝ (TriangularCovering.faceNormal 0) v = -2 * embedding v 1 := by
    simp [TriangularCovering.inner_coord, TriangularCovering.faceNormal,
      TriangularCovering.H, embedding]
    field_simp
    ring_nf
    norm_num [sqrt_two_sq]
    ring
  have h1 : inner ℝ (TriangularCovering.faceNormal 1) v = -2 * embedding v 0 := by
    simp [TriangularCovering.inner_coord, TriangularCovering.faceNormal,
      TriangularCovering.H, embedding]
    field_simp
    ring_nf
    norm_num [sqrt_two_sq]
    ring
  have h2 : inner ℝ (TriangularCovering.faceNormal 2) v = -2 * embedding v 3 := by
    simp [TriangularCovering.inner_coord, TriangularCovering.faceNormal,
      TriangularCovering.H, embedding]
    field_simp
    ring_nf
    norm_num [sqrt_two_sq]
    ring
  have h3 : inner ℝ (TriangularCovering.faceNormal 3) v = -2 * embedding v 2 := by
    simp [TriangularCovering.inner_coord, TriangularCovering.faceNormal,
      TriangularCovering.H, embedding]
    field_simp
    ring_nf
    norm_num [sqrt_two_sq]
    ring
  rw [TriangularCovering.shadowArea_abs_sum hv]
  simp only [Fin.sum_univ_four, h0, h1, h2, h3, abs_mul]
  norm_num
  ring

theorem shadowArea_formula (u : Barycentric) (hu : ‖u‖ = 1)
    (hsum : ∑ i : Fin 4, u i = 0) :
    shadowArea u = (1 / 2 : ℝ) * ∑ i : Fin 4, |u i| := by
  have hv : ‖inverse u‖ = 1 := (inverse_norm u hsum).trans hu
  calc
    shadowArea u = shadowArea (embedding (inverse u)) := by rw [embedding_inverse u hsum]
    _ = (1 / 2 : ℝ) * TriangularCovering.shadowArea (inverse u) := shadowArea_embedding _
    _ = (1 / 2 : ℝ) * ∑ i : Fin 4, |u i| := by
      rw [physical_shadow_eq_abs_embedding _ hv, embedding_inverse u hsum]

theorem shadowArea_lower_bound (u : Barycentric) (hu : ‖u‖ = 1)
    (hsum : ∑ i : Fin 4, u i = 0) : 1 / Real.sqrt 2 ≤ shadowArea u := by
  rw [shadowArea_formula u hu hsum]
  exact CylinderNormalFrame.barycentricCost_lower_bound u hu hsum

theorem shadowArea_isLeast :
    IsLeast {a : ℝ | ∃ u : Barycentric,
      ‖u‖ = 1 ∧ ∑ i : Fin 4, u i = 0 ∧ a = shadowArea u} (1 / Real.sqrt 2) := by
  constructor
  · refine ⟨CylinderNormalFrame.barycentricEdge, CylinderNormalFrame.barycentricEdge_unit,
      CylinderNormalFrame.barycentricEdge_sum, ?_⟩
    rw [shadowArea_formula _ CylinderNormalFrame.barycentricEdge_unit
      CylinderNormalFrame.barycentricEdge_sum]
    exact CylinderNormalFrame.barycentricCost_edge.symm
  · rintro a ⟨u,hu,hsum,rfl⟩
    exact shadowArea_lower_bound u hu hsum

theorem projectionStatement : ProjectionStatement :=
  ⟨shadowArea_formula, shadowArea_isLeast⟩

end CylinderBarycentricMetric

end

end OAI

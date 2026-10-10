import OAI.Geometry.CylinderCovering.Rational.TetrahedronGeometryDefinitions
import OAI.Geometry.CylinderCovering.Simplex.ProjectionIdentity

namespace OAI

noncomputable section
open Set
namespace RationalSimilarity

private theorem sqrtTwo_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
private theorem sqrtTwo_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private theorem h_eq_sqrt_half : h = Real.sqrt 2 / 2 := by
  unfold h
  apply (div_eq_div_iff sqrtTwo_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)).mpr
  nlinarith [sqrtTwo_sq]

theorem uncenteredTetrahedron_eq_dilation :
    uncenteredTetrahedron = (fun z : Space => Real.sqrt 2 • z) '' TriangularCovering.K := by
  ext z
  constructor
  · rintro ⟨hz0, hz2, hy, hx⟩
    rw [h_eq_sqrt_half] at hx hy
    refine ⟨TriangularCovering.point (z 0 / Real.sqrt 2) (z 1 / Real.sqrt 2) (z 2 / 2), ?_, ?_⟩
    · refine ⟨z 0 / Real.sqrt 2, z 1 / Real.sqrt 2, z 2 / 2,
        by linarith, by linarith, ?_, ?_, rfl⟩
      · rw [abs_div, abs_of_pos sqrtTwo_pos]
        apply (div_le_iff₀ sqrtTwo_pos).mpr
        nlinarith only [hx]
      · rw [abs_div, abs_of_pos sqrtTwo_pos]
        apply (div_le_iff₀ sqrtTwo_pos).mpr
        nlinarith only [hy]
    · ext i
      fin_cases i
      · change Real.sqrt 2 * (z 0 / Real.sqrt 2) = z 0
        field_simp [sqrtTwo_pos.ne']
      · change Real.sqrt 2 * (z 1 / Real.sqrt 2) = z 1
        field_simp [sqrtTwo_pos.ne']
      · change Real.sqrt 2 * (Real.sqrt 2 * (z 2 / 2)) = z 2
        nlinarith [sqrtTwo_sq]
  · rintro ⟨w, ⟨x,y,t,ht0,ht1,hx,hy,rfl⟩, rfl⟩
    have hs : Real.sqrt 2 * (Real.sqrt 2 * t) = 2 * t := by
      rw [← mul_assoc, ← pow_two, sqrtTwo_sq]
    change 0 ≤ Real.sqrt 2 * (Real.sqrt 2 * t) ∧
      Real.sqrt 2 * (Real.sqrt 2 * t) ≤ 2 ∧
      |Real.sqrt 2 * y| ≤ h * (Real.sqrt 2 * (Real.sqrt 2 * t)) ∧
      |Real.sqrt 2 * x| ≤ h * (2 - Real.sqrt 2 * (Real.sqrt 2 * t))
    rw [hs, h_eq_sqrt_half, abs_mul, abs_mul, abs_of_pos sqrtTwo_pos]
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · nlinarith only [mul_le_mul_of_nonneg_left hy sqrtTwo_pos.le]
    · nlinarith only [mul_le_mul_of_nonneg_left hx sqrtTwo_pos.le]

private def dilation : Space →ᵃ[ℝ] Space :=
  CylinderCovering.Similarity.affineMap 0 (Real.sqrt 2) (LinearIsometryEquiv.refl ℝ Space)

private theorem dilation_apply (z : Space) : dilation z = Real.sqrt 2 • z := by
  simp [dilation, CylinderCovering.Similarity.affineMap]

private theorem dilation_injective : Function.Injective dilation :=
  CylinderCovering.Similarity.map_injective 0 sqrtTwo_pos.ne' (LinearIsometryEquiv.refl ℝ Space)

private theorem vertices_eq_dilation :
    uncenteredVertices = dilation ∘ TriangularCovering.tetraVertices := by
  funext i
  rw [Function.comp_apply, dilation_apply]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [uncenteredVertices, TriangularCovering.tetraVertices, TriangularCovering.point,
      TriangularCovering.H]

theorem uncenteredVertices_affineIndependent : AffineIndependent ℝ uncenteredVertices := by
  rw [vertices_eq_dilation]
  exact TriangularCovering.tetra_affineIndependent.map' dilation dilation_injective

theorem uncenteredVertices_edge {i j : Fin 4} (hij : i ≠ j) :
    dist (uncenteredVertices i) (uncenteredVertices j) = 2 * Real.sqrt 2 := by
  rw [vertices_eq_dilation]
  simp only [Function.comp_apply, dilation_apply]
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos sqrtTwo_pos,
    ← dist_eq_norm, TriangularCovering.tetra_edge_length hij]
  ring

theorem uncenteredTetrahedron_eq_convexHull :
    uncenteredTetrahedron = convexHull ℝ (range uncenteredVertices) := by
  rw [vertices_eq_dilation, range_comp, ← dilation.image_convexHull,
    ← TriangularCovering.K_eq_convexHull, uncenteredTetrahedron_eq_dilation]
  congr 1
  funext z
  exact (dilation_apply z).symm

theorem uncenteredTetrahedron_regular :
    CylinderCovering.IsRegularTetrahedron uncenteredTetrahedron :=
  ⟨uncenteredVertices, uncenteredVertices_affineIndependent, 2 * Real.sqrt 2,
    by positivity, fun _ _ hij => uncenteredVertices_edge hij,
    uncenteredTetrahedron_eq_convexHull⟩

theorem uncenteredTetrahedron_geometry : UncenteredTetrahedronGeometryStatement := by
  have he : 0 < 2 * Real.sqrt (2 : ℝ) := by positivity
  have hm := CylinderCovering.regularMetricNormalization_result uncenteredVertices
    uncenteredVertices_affineIndependent (2 * Real.sqrt 2) he
    (fun _ _ hij => uncenteredVertices_edge hij)
  rw [← uncenteredTetrahedron_eq_convexHull] at hm
  refine ⟨uncenteredVertices_affineIndependent, fun _ _ hij => uncenteredVertices_edge hij,
    uncenteredTetrahedron_eq_convexHull, uncenteredTetrahedron_regular, hm.1, ?_, ?_⟩
  · rw [hm.2.1]
    field_simp
    nlinarith [sqrtTwo_sq]
  · have hmin := hm.2.2
    have hs : Real.sqrt (2 : ℝ) ≠ 0 := sqrtTwo_pos.ne'
    field_simp [hs] at hmin
    nlinarith [sqrtTwo_sq]

end RationalSimilarity

end

end OAI

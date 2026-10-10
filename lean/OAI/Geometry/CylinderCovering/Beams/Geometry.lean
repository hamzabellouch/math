import OAI.Geometry.CylinderCovering.Beams.FullDefinitions
import OAI.Geometry.CylinderCovering.Convexity.RegularCounterexamples
import OAI.Geometry.CylinderCovering.Simplex.ProjectionIdentity

namespace OAI

noncomputable section
open Set MeasureTheory
namespace ShortenedBeam
open CylinderCovering

private lemma root_two_ne : Real.sqrt 2 ≠ 0 := by positivity
private lemma root_two_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)

def normalizationMap : Space → Space :=
  Similarity.map (point 0 0 (-1)) (Real.sqrt 2) (LinearIsometryEquiv.refl ℝ Space)

lemma normalizationMap_point (x y t : ℝ) :
    normalizationMap (TriangularCovering.point x y t) = point (2*x) (2*y) (2*t-1) := by
  ext i
  fin_cases i <;>
    simp [normalizationMap, Similarity.map, point, TriangularCovering.point,
      TriangularCovering.H] <;> field_simp <;> ring_nf <;> simp <;> ring

lemma tetrahedron_eq_normalization :
    tetrahedron = normalizationMap '' TriangularCovering.K := by
  ext z
  constructor
  · rintro ⟨x,y,t,ht,hx,hy,rfl⟩
    refine ⟨TriangularCovering.point (x/2) (y/2) ((t+1)/2), ?_, ?_⟩
    · refine ⟨x/2,y/2,(t+1)/2,?_,?_,?_,?_,rfl⟩
      · linarith [(abs_le.mp ht).1]
      · linarith [(abs_le.mp ht).2]
      · rw [abs_div]; norm_num; linarith
      · rw [abs_div]; norm_num; linarith
    · rw [normalizationMap_point]
      congr 1 <;> ring
  · rintro ⟨_,⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,rfl⟩
    rw [normalizationMap_point]
    refine ⟨2*x,2*y,2*t-1,?_,?_,?_,rfl⟩
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_mul]; norm_num; linarith
    · rw [abs_mul]; norm_num; linarith

lemma vertices_eq_normalization :
    vertices = normalizationMap ∘ TriangularCovering.tetraVertices := by
  funext i
  fin_cases i <;>
    norm_num [vertices, TriangularCovering.tetraVertices, Function.comp_def,
      normalizationMap_point]

lemma tetrahedron_eq_vertices : tetrahedron = convexHull ℝ (range vertices) := by
  let f := Similarity.affineMap (point 0 0 (-1)) (Real.sqrt 2)
    (LinearIsometryEquiv.refl ℝ Space)
  rw [tetrahedron_eq_normalization, TriangularCovering.K_eq_convexHull,
    vertices_eq_normalization]
  change f '' convexHull ℝ (range TriangularCovering.tetraVertices) =
    convexHull ℝ (range (f ∘ TriangularCovering.tetraVertices))
  rw [f.image_convexHull, range_comp]

lemma vertices_affineIndependent : AffineIndependent ℝ vertices := by
  rw [vertices_eq_normalization]
  exact TriangularCovering.tetra_affineIndependent.map'
    (Similarity.affineMap (point 0 0 (-1)) (Real.sqrt 2)
      (LinearIsometryEquiv.refl ℝ Space))
    (Similarity.map_injective _ root_two_ne _)

lemma vertices_edge_length {i j : Fin 4} (hij : i ≠ j) :
    dist (vertices i) (vertices j) = 2*Real.sqrt 2 := by
  rw [vertices_eq_normalization]
  simp only [Function.comp_apply, normalizationMap, Similarity.map,
    dist_add_left]
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Real.sqrt 2)]
  change Real.sqrt 2 * dist (TriangularCovering.tetraVertices i)
    (TriangularCovering.tetraVertices j) = _
  rw [TriangularCovering.tetra_edge_length hij]
  ring

lemma tetrahedron_minimum_shadow :
    minimumShadowArea tetrahedron = 2*Real.sqrt 2 := by
  change Similarity.minimumArea tetrahedron = _
  rw [tetrahedron_eq_normalization]
  change Similarity.minimumArea (Similarity.map _ _ _ '' TriangularCovering.K) = _
  rw [Similarity.minimumArea_map _ _ root_two_ne]
  change (Real.sqrt 2)^2 * TriangularCovering.A_min = _
  rw [root_two_sq, TriangularCovering.projection_minimum]
  rfl

lemma tetrahedron_regular : IsRegularTetrahedron tetrahedron := by
  exact ⟨vertices, vertices_affineIndependent, 2*Real.sqrt 2, by positivity,
    fun _ _ h => vertices_edge_length h, tetrahedron_eq_vertices⟩

theorem geometry_of_volume (hvol : volume.real tetrahedron = 8/3) : GeometryStatement :=
  ⟨tetrahedron_eq_vertices, vertices_affineIndependent,
    fun _ _ h => vertices_edge_length h, hvol, tetrahedron_minimum_shadow⟩

lemma tetrahedron_volume : volume.real tetrahedron = 8/3 := by
  rw [tetrahedron_eq_vertices]
  rw [CylinderCovering.regular_tetrahedron_volume vertices vertices_affineIndependent
    (show 0 < 2*Real.sqrt 2 by positivity) (fun _ _ h => vertices_edge_length h)]
  have hs : Real.sqrt 2 ≠ 0 := root_two_ne
  field_simp
  nlinarith [root_two_sq]

theorem geometryStatement : GeometryStatement := geometry_of_volume tetrahedron_volume

end ShortenedBeam

end

end OAI

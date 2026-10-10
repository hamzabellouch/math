import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.CylinderCovering.Physical.Coverage

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.HalfheightFinite

theorem height_mem_Icc {X Y Z : ℝ} (hX : |X| ≤ 1 - Z) (hY : |Y| ≤ Z) :
    Z ∈ Icc (0 : ℝ) 1 := by
  constructor <;> linarith [abs_nonneg X, abs_nonneg Y]

theorem tetrahedron_eq_unitEdge : tetrahedron = UnitEdgeFootprints.tetrahedron := by
  ext z
  constructor
  · rintro ⟨X, Y, Z, hX, hY, rfl⟩
    refine ⟨Z, height_mem_Icc hX hY, rfl, ?_, ?_⟩
    · change |X / 2| ≤ (1 - Z) / 2
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · change |Y / 2| ≤ Z / 2
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
  · rintro ⟨Z, hZ, hz, hX, hY⟩
    refine ⟨2 * z 0, 2 * z 1, Z, ?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · ext i
      fin_cases i
      · simp [point]
      · simp [point]
      · change z 2 = height * Z
        exact hz

theorem tetrahedron_similarity : tetrahedron =
    Similarity.map (0 : Space) (1 / 2) (LinearIsometryEquiv.refl ℝ Space) ''
      TriangularCovering.K := by
  rw [tetrahedron_eq_unitEdge]
  exact UnitEdgeFootprints.tetrahedron_similarity

theorem unit_edge_geometry :
    ∃ v : Fin 4 → Space, AffineIndependent ℝ v ∧
      (∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = 1) ∧
      tetrahedron = convexHull ℝ (range v) := by
  let f := AffineMap.homothety (0 : Space) (1 / 2 : ℝ)
  have hf : Function.Injective f :=
    AffineMap.homothety_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  refine ⟨f ∘ TriangularCovering.tetraVertices,
    TriangularCovering.tetra_affineIndependent.map' f hf, ?_, ?_⟩
  · intro i j hij
    change dist (f (TriangularCovering.tetraVertices i))
      (f (TriangularCovering.tetraVertices j)) = 1
    simp only [f, AffineMap.homothety_apply, vsub_eq_sub, sub_zero,
      vadd_eq_add, add_zero]
    rw [dist_smul₀, Real.norm_eq_abs,
      TriangularCovering.tetra_edge_length hij]
    norm_num
  · have hmap : Similarity.map (0 : Space) (1 / 2)
        (LinearIsometryEquiv.refl ℝ Space) = f := by
      funext z
      simp [Similarity.map, f, AffineMap.homothety_apply]
    rw [tetrahedron_similarity, TriangularCovering.K_eq_convexHull,
      hmap, f.image_convexHull, range_comp]

theorem isRegularTetrahedron : CylinderCovering.IsRegularTetrahedron tetrahedron := by
  obtain ⟨v, hv, hd, hK⟩ := unit_edge_geometry
  exact ⟨v, hv, 1, by norm_num, hd, hK⟩

theorem minimum_area : Similarity.minimumArea tetrahedron = height / 2 := by
  rw [tetrahedron_eq_unitEdge]
  exact UnitEdgeFootprints.minimum_area

theorem strict_cost_iff_half_minimum (cost : ℝ) :
    cost < height / 4 ↔ cost < Similarity.minimumArea tetrahedron / 2 := by
  rw [minimum_area]
  ring_nf

end CylinderCovering.HalfheightFinite

end

end OAI

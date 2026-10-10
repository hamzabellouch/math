import OAI.Geometry.CylinderCovering.Cubic.RescalingDefinitions
import OAI.Geometry.CylinderCovering.Cubic.Rescaling
import OAI.Geometry.CylinderCovering.Angular.CubicFamily
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace CylinderCovering.Cubic
open TriangularCovering

private abbrev identityIsometry : Space ≃ₗᵢ[ℝ] Space := LinearIsometryEquiv.refl ℝ Space

lemma contraction_point (x y z : ℝ) :
    contraction (point x y z) = point (x / 2) (y / 2) ((z + 1) / 2) := by
  ext i
  fin_cases i <;> dsimp [contraction, point] <;> ring

lemma contraction_double_sub (p : Space) :
    contraction ((2 : ℝ) • p - point 0 0 1) = p := by
  have hs : point 0 0 (1 / 2) = (1 / 2 : ℝ) • point 0 0 1 := by
    ext i
    fin_cases i <;> dsimp [point] <;> ring
  rw [contraction, hs]
  module

lemma contraction_K4 : contraction '' K4 = K := by
  rw [K4_eq_double_sub, Set.image_image]
  have hf : (fun p : Space => contraction ((2 : ℝ) • p - point 0 0 1)) = id := by
    funext p
    exact contraction_double_sub p
  rw [hf, Set.image_id]

def contractCylinder (c : TriCylinder) : TriCylinder where
  axis := c.axis
  base := contractedBaseMap c.axis '' c.base
  unit_axis := c.unit_axis
  perpendicular := by
    exact Similarity.transportedBase_perpendicular c.unit_axis c.perpendicular
      (point 0 0 (1 / 2)) (1 / 2) identityIsometry
  triangular := Similarity.transportedBase_triangular c.triangular c.axis
    (point 0 0 (1 / 2)) (by norm_num : (1 / 2 : ℝ) ≠ 0) identityIsometry
  compact := Similarity.transportedBase_compact c.compact c.axis
    (point 0 0 (1 / 2)) (1 / 2) identityIsometry
  convex := Similarity.transportedBase_convex c.convex c.axis
    (point 0 0 (1 / 2)) (1 / 2) identityIsometry
  measurable := (Similarity.transportedBase_compact c.compact c.axis
    (point 0 0 (1 / 2)) (1 / 2) identityIsometry).measurableSet
  finite_area := Similarity.transportedBase_finite c.finite_area c.axis
    (point 0 0 (1 / 2)) (by norm_num : (1 / 2 : ℝ) ≠ 0) identityIsometry

lemma contractCylinder_axis (c : TriCylinder) : (contractCylinder c).axis = c.axis := rfl

lemma contractCylinder_carrier (c : TriCylinder) :
    contraction '' c.carrier = (contractCylinder c).carrier := by
  exact Similarity.carrier_image c.base c.axis (point 0 0 (1 / 2))
    (by norm_num : (1 / 2 : ℝ) ≠ 0) identityIsometry

lemma contractCylinder_area (c : TriCylinder) :
    area (contractCylinder c).base = area c.base / 4 := by
  change Similarity.area (Similarity.transportedBase c.base c.axis
    (point 0 0 (1 / 2)) (1 / 2) identityIsometry) = Similarity.area c.base / 4
  rw [Similarity.area_transportedBase c.base c.axis (point 0 0 (1 / 2))
    (by norm_num : (1 / 2 : ℝ) ≠ 0) identityIsometry]
  ring

lemma contractFamily_covers {m : ℕ} {c : Fin m → TriCylinder} (hc : CoversK4 c) :
    Covers (fun i => contractCylinder (c i)) := by
  intro p hp
  rw [← contraction_K4] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨i, hi⟩ := hc q hq
  refine ⟨i, ?_⟩
  rw [← contractCylinder_carrier]
  exact ⟨q, hi, rfl⟩

lemma contractFamily_total {m : ℕ} (c : Fin m → TriCylinder) :
    totalArea (fun i => contractCylinder (c i)) = totalArea c / 4 := by
  simp only [totalArea, contractCylinder_area, Finset.sum_div]

theorem rescaledFiniteCover_proof : RescaledFiniteCoverStatement := by
  intro τ hτ hτ1
  refine ⟨rescaled_count τ, ?_⟩
  obtain ⟨c, hc, harea, hprescribed⟩ := finiteCover_proof (τ / 2)
    (by linarith) (by linarith)
  refine ⟨fun i => contractCylinder (c i), contractFamily_covers hc, ?_, ?_⟩
  · rw [contractFamily_total, harea]
  · exact ⟨c, hprescribed, fun i => ⟨rfl, rfl⟩⟩

end CylinderCovering.Cubic

end

end OAI

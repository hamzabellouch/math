import OAI.Geometry.TriangularCovering.Basic
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace TriangularCovering

namespace TriCylinder

def similarity (c : TriCylinder) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) : TriCylinder where
  axis := L c.axis
  base := CylinderCovering.Similarity.transportedBase c.base c.axis t r L
  unit_axis := by simpa using c.unit_axis
  perpendicular := CylinderCovering.Similarity.transportedBase_perpendicular
    c.unit_axis c.perpendicular t r L
  triangular := CylinderCovering.Similarity.transportedBase_triangular c.triangular c.axis t hr L
  compact := CylinderCovering.Similarity.transportedBase_compact c.compact c.axis t r L
  convex := CylinderCovering.Similarity.transportedBase_convex c.convex c.axis t r L
  measurable := (CylinderCovering.Similarity.transportedBase_compact c.compact c.axis t r L).measurableSet
  finite_area := CylinderCovering.Similarity.transportedBase_finite c.finite_area c.axis t hr L

lemma similarity_carrier (c : TriCylinder) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) :
    (c.similarity t hr L).carrier = CylinderCovering.Similarity.map t r L '' c.carrier :=
  (CylinderCovering.Similarity.carrier_image c.base c.axis t hr L).symm

lemma similarity_area (c : TriCylinder) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) :
    area (c.similarity t hr L).base = r ^ 2 * area c.base :=
  CylinderCovering.Similarity.area_transportedBase c.base c.axis t hr L

end TriCylinder

lemma similarity_totalArea {m : ℕ} (c : Fin m → TriCylinder)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    totalArea (fun i => (c i).similarity t hr L) = r ^ 2 * totalArea c := by
  simp only [totalArea, TriCylinder.similarity_area, Finset.mul_sum]

lemma similarity_covers {m : ℕ} (c : Fin m → TriCylinder) (hc : Covers c)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    ∀ x ∈ CylinderCovering.Similarity.map t r L '' K,
      ∃ i, x ∈ ((c i).similarity t hr L).carrier := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨i, hi⟩ := hc y hy
  refine ⟨i, ?_⟩
  rw [TriCylinder.similarity_carrier]
  exact ⟨y, hi, rfl⟩

lemma similarity_relativeCost {m : ℕ} (c : Fin m → TriCylinder)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    (∑ i, area ((c i).similarity t hr L).base /
      CylinderCovering.Similarity.shadowArea
        (CylinderCovering.Similarity.map t r L '' K) ((c i).similarity t hr L).axis) =
      relativeCost c := by
  unfold relativeCost
  apply Finset.sum_congr rfl
  intro i hi
  exact CylinderCovering.Similarity.areaRatio_map (c i).base K (c i).axis t hr L

theorem triangle_cover_similarity {m : ℕ} (c : Fin m → TriCylinder)
    (hc : Covers c) (harea : totalArea c < A_min / 2)
    (hrelative : relativeCost c < 1 / 2)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    ∃ d : Fin m → TriCylinder,
      (∀ x ∈ CylinderCovering.Similarity.map t r L '' K, ∃ i, x ∈ (d i).carrier) ∧
      totalArea d < CylinderCovering.Similarity.minimumArea
        (CylinderCovering.Similarity.map t r L '' K) / 2 ∧
      (∑ i, area (d i).base / CylinderCovering.Similarity.shadowArea
        (CylinderCovering.Similarity.map t r L '' K) (d i).axis) < 1 / 2 := by
  refine ⟨fun i => (c i).similarity t hr L, similarity_covers c hc t hr L, ?_, ?_⟩
  · rw [similarity_totalArea, CylinderCovering.Similarity.minimumArea_map K t hr L]
    change r ^ 2 * totalArea c < r ^ 2 * A_min / 2
    nlinarith [mul_lt_mul_of_pos_left harea (sq_pos_of_ne_zero hr)]
  · rw [similarity_relativeCost]
    exact hrelative

end TriangularCovering

end

end OAI

import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.AffinePlaneNormalFrame
import OAI.Analysis.RieszRectifiability.Flatness.AffineAnchorBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module EuclideanGeometry
open scoped BigOperators

theorem plane_distance_bound_from_basis_anchors {n d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) (hW : IsAffineNPlane n W)
    (a : Ambient d) (ha : a ∈ S) (b : Basis (Fin n) ℝ S.direction)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbase : infDist a (W : Set (Ambient d)) ≤ ε)
    (hvertices : ∀ i, infDist (a + (b i : Ambient d)) (W : Set (Ambient d)) ≤ ε)
    (x : Ambient d) (hx : x ∈ S) :
    infDist x (W : Set (Ambient d)) ≤
      ε * (1 + 2 * ((n : ℝ) * basisCoordinateNorm b * ‖x - a‖)) := by
  obtain ⟨aw, _haw, _hnorm, _Lw, _hLw, Nw, _horth, _hsplit, hdist⟩ :=
    exists_affine_plane_normal_frame W hW
  let F := Nw.toContinuousLinearMap.adjoint
  have hF : ∀ y, ‖-F aw + F y‖ = infDist y (W : Set (Ambient d)) := by
    intro y
    rw [hdist y]
    change ‖-F aw + F y‖ = ‖F (y - aw)‖
    rw [map_sub]
    congr 1
    abel
  let u : S.direction := ⟨x - a, AffineSubspace.vsub_mem_direction hx ha⟩
  have hrep : (∑ i, b.equivFun u i • (b i : Ambient d)) = x - a := by
    have h := congrArg (fun v : S.direction => (v : Ambient d)) (b.sum_equivFun u)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using! h
  have hxa : x = a + ∑ i, b.equivFun u i • (b i : Ambient d) := by rw [hrep]; abel
  have hbound := affine_map_norm_bound_from_anchors (-F aw) F a
    (fun i => (b i : Ambient d)) (b.equivFun u) ε
    (by simpa only [hF] using! hbase) (by intro i; simpa only [hF] using! hvertices i)
  rw [← hxa, hF] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (basis_coordinate_l1_bound b u)
      (by norm_num : (0 : ℝ) ≤ 2))) hε)

theorem infDist_projection_le_sum {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (W : Set (Ambient d)) (x : Ambient d) :
    infDist (orthogonalProjection S x : Ambient d) W ≤
      infDist x (S : Set (Ambient d)) + infDist x W := by
  calc
    _ ≤ infDist x W + dist (orthogonalProjection S x : Ambient d) x :=
      infDist_le_infDist_add_dist
    _ = _ := by
      rw [dist_comm, dist_orthogonalProjection_eq_infDist]
      exact add_comm _ _

theorem plane_distance_bound_from_projected_anchors {n d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) [Nonempty S] (hW : IsAffineNPlane n W)
    (p₀ : Ambient d) (p : Fin n → Ambient d)
    (a : Ambient d) (ha : a = (orthogonalProjection S p₀ : Ambient d))
    (b : Basis (Fin n) ℝ S.direction)
    (hvertices : ∀ i, a + (b i : Ambient d) = (orthogonalProjection S (p i) : Ambient d))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbase : infDist p₀ (S : Set (Ambient d)) + infDist p₀ (W : Set (Ambient d)) ≤ ε)
    (hpoints : ∀ i, infDist (p i) (S : Set (Ambient d)) +
      infDist (p i) (W : Set (Ambient d)) ≤ ε)
    (x : Ambient d) (hx : x ∈ S) :
    infDist x (W : Set (Ambient d)) ≤
      ε * (1 + 2 * ((n : ℝ) * basisCoordinateNorm b * ‖x - a‖)) := by
  apply plane_distance_bound_from_basis_anchors S W hW a
    (ha ▸ orthogonalProjection_mem p₀) b ε hε _ _ x hx
  · rw [ha]
    exact (infDist_projection_le_sum S (W : Set (Ambient d)) p₀).trans hbase
  · intro i
    rw [hvertices i]
    exact (infDist_projection_le_sum S (W : Set (Ambient d)) (p i)).trans (hpoints i)

end

end RieszRectifiability

end OAI

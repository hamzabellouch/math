import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlaneAnchorComparison
import OAI.Analysis.RieszRectifiability.Kernel.AnchorPerturbation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module EuclideanGeometry
open scoped BigOperators

theorem plane_distance_bound_from_conditioned_generators {n d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (a : Ambient d) (ha : a ∈ S) (v : Fin n → Ambient d)
    (hv : ∀ i, v i ∈ S.direction) (K ε : ℝ) (hε : 0 ≤ ε)
    (hcoeff : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ K * ‖∑ i, t i • v i‖)
    (hbase : infDist a (W : Set (Ambient d)) ≤ ε)
    (hvertices : ∀ i, infDist (a + v i) (W : Set (Ambient d)) ≤ ε)
    (x : Ambient d) (hx : x ∈ S) :
    infDist x (W : Set (Ambient d)) ≤ ε * (1 + 2 * (K * ‖x - a‖)) := by
  have hlin := linearIndependent_of_coordinate_bound v K hcoeff
  have hsub : Submodule.span ℝ (range v) ≤ S.direction := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact hv i
  have hdim : finrank ℝ (Submodule.span ℝ (range v)) = n := by
    simpa only [Fintype.card_fin] using! finrank_span_eq_card hlin
  have hspan : Submodule.span ℝ (range v) = S.direction :=
    Submodule.eq_of_le_of_finrank_eq hsub (hdim.trans hS.2.symm)
  have hxspan : x - a ∈ Submodule.span ℝ (range v) := by
    rw [hspan]
    exact AffineSubspace.vsub_mem_direction hx ha
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hxspan
  have hxa : x = a + ∑ i, t i • v i := by rw [ht]; abel
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
  have hb := affine_map_norm_bound_from_anchors (-F aw) F a v t ε
    (by simpa only [hF] using! hbase) (by intro i; simpa only [hF] using! hvertices i)
  rw [← hxa, hF] at hb
  have hc := hcoeff t
  rw [ht] at hc
  exact hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))) hε)

theorem plane_distance_bound_from_conditioned_support_anchors {n d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (p0 : Ambient d) (p : Fin n → Ambient d) (K η : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hsmall : K * (2 * η) ≤ 1 / 2)
    (hcoeff : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ K * ‖∑ i, t i • (p i - p0)‖)
    (hbase : infDist p0 (S : Set (Ambient d)) ≤ η ∧ infDist p0 (W : Set (Ambient d)) ≤ η)
    (hpoints : ∀ i, infDist (p i) (S : Set (Ambient d)) ≤ η ∧
      infDist (p i) (W : Set (Ambient d)) ≤ η)
    (x : Ambient d) (hx : x ∈ S) :
    infDist x (W : Set (Ambient d)) ≤
      2 * η * (1 + 4 * K * ‖x - (orthogonalProjection S p0 : Ambient d)‖) := by
  let a : Ambient d := orthogonalProjection S p0
  let v : Fin n → Ambient d := fun i => (orthogonalProjection S (p i) : Ambient d) - a
  have hclose : ∀ i, ‖v i - (p i - p0)‖ ≤ 2 * η := by
    intro i
    exact (projected_anchor_perturbation_bound S p0 (p i)).trans
      (by linarith [(hpoints i).1, hbase.1])
  have hc : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ (2 * K) * ‖∑ i, t i • v i‖ :=
    coordinate_bound_under_perturbation (fun i => p i - p0) v K (2 * η) hK hsmall hclose hcoeff
  have hv : ∀ i, v i ∈ S.direction := fun i =>
    AffineSubspace.vsub_mem_direction (orthogonalProjection_mem (p i)) (orthogonalProjection_mem p0)
  have hb : infDist a (W : Set (Ambient d)) ≤ 2 * η :=
    (infDist_projection_le_sum S (W : Set (Ambient d)) p0).trans (by linarith [hbase.1, hbase.2])
  have hvfit : ∀ i, infDist (a + v i) (W : Set (Ambient d)) ≤ 2 * η := by
    intro i
    have heq : a + v i = (orthogonalProjection S (p i) : Ambient d) := by dsimp only [v]; abel
    rw [heq]
    exact (infDist_projection_le_sum S (W : Set (Ambient d)) (p i)).trans
      (by linarith [(hpoints i).1, (hpoints i).2])
  have h := plane_distance_bound_from_conditioned_generators S W hS hW a
    (orthogonalProjection_mem p0) v hv (2 * K) (2 * η) (by positivity) hc hb hvfit x hx
  convert! h using 1
  ring

end

end RieszRectifiability

end OAI

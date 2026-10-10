import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.InitialAffineCharts
import OAI.Analysis.RieszRectifiability.Surfaces.PlaneDiskLowerArea

namespace OAI

/-!
Positive-dimensional affine planes contain prescribed-distance points away from a chosen center.
Affine disk coordinates convert this separation into exterior disk patches.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_affine_point_away_from_center {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hdim : 0 < Module.finrank ℝ S.direction)
    (y z : Ambient d) (hy : y ∈ S) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ q ∈ S, dist q y = ρ ∧ ρ ≤ dist q z := by
  let : Nontrivial S.direction := Module.nontrivial_of_finrank_pos hdim
  obtain ⟨v, hv⟩ := exists_norm_eq S.direction hρ
  have hv' : ‖(v : Ambient d)‖ = ρ := hv
  have hp : (v : Ambient d) + y ∈ S :=
    AffineSubspace.vadd_mem_of_mem_direction v.property hy
  have hm : -(v : Ambient d) + y ∈ S :=
    AffineSubspace.vadd_mem_of_mem_direction (S.direction.neg_mem v.property) hy
  have hpd : dist ((v : Ambient d) + y) y = ρ := by
    simpa only [dist_eq_norm, add_sub_cancel_right] using! hv'
  have hmd : dist (-(v : Ambient d) + y) y = ρ := by
    simpa only [dist_eq_norm, add_sub_cancel_right, norm_neg] using! hv'
  have hdiam : dist ((v : Ambient d) + y) (-(v : Ambient d) + y) = 2 * ρ := by
    rw [dist_eq_norm, show (v : Ambient d) + y - (-(v : Ambient d) + y) =
      (2 : ℝ) • (v : Ambient d) by module, norm_smul, hv']
    norm_num
  by_cases hfar : ρ ≤ dist ((v : Ambient d) + y) z
  · exact ⟨(v : Ambient d) + y, hp, hpd, hfar⟩
  · refine ⟨-(v : Ambient d) + y, hm, hmd, ?_⟩
    have ht := dist_triangle_right ((v : Ambient d) + y) (-(v : Ambient d) + y) z
    rw [hdiam] at ht
    linarith [lt_of_not_ge hfar]

theorem exists_affine_exterior_disk {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hdim : 0 < Module.finrank ℝ S.direction)
    (p y z : Ambient d) (hy : y ∈ S) (r : ℝ) (hr : 0 < r)
    (hnear : dist y p ≤ r / 8) :
    ∃ a : S.direction, ∃ g : closedBall a (r / 8) → Ambient d,
      LipschitzWith 1 g ∧ AntilipschitzWith 1 g ∧
      Set.range g ⊆ (S : Set (Ambient d)) ∩ closedBall p r ∧
      ∀ x ∈ Set.range g, 3 * r / 8 ≤ dist x z := by
  obtain ⟨q, hq, hqy, hqz⟩ := exists_affine_point_away_from_center S hdim y z hy
    (r / 2) (by positivity)
  obtain ⟨g, hLip, _, hcoords, _⟩ := exists_located_affine_plane_disk_chart S ⟨y, hy⟩ q (r / 8)
  have hloc (u) : dist (g u) q ≤ r / 8 := by
    simpa only [infDist_zero_of_mem hq, add_zero] using! (hcoords u).2.2
  have hsep : AntilipschitzWith 1 g := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    simp only [NNReal.coe_one, one_mul]
    change dist u.val v.val ≤ dist (g u) (g v)
    rw [← (hcoords u).2.1, ← (hcoords v).2.1]
    have h := S.direction.norm_starProjection_apply_le (g u - g v)
    rw [map_sub] at h
    exact h
  refine ⟨S.direction.orthogonalProjectionOnto q, g, hLip, hsep, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    refine ⟨(hcoords u).1, ?_⟩
    have h1 := dist_triangle (g u) q y
    have h2 := dist_triangle (g u) y p
    change dist (g u) p ≤ r
    linarith [hloc u]
  · rintro _ ⟨u, rfl⟩
    have ht := dist_triangle q (g u) z
    rw [dist_comm q (g u)] at ht
    linarith [hloc u]

end

end RieszRectifiability

end OAI

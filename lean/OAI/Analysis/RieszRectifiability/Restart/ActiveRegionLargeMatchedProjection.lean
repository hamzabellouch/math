import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.ContinuousChartInnerCoverage
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionAllScaleForwardFlatness

namespace OAI

/-!
# Matched projection at large radii

The root plane approximates the active-region limit surface at radii comparable
to or larger than the root scale. A continuous chart close to this plane gives
projection coverage of an inner disk, with the original quantitative constants.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_region_large_matched_projection {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 72057594037927936)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r)
    (hrlarge : latticeRadius R k / 2097152 ≤ r) :
    ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
      (∀ x ∈ Set.range f ∩ closedBall p (1024 * r),
        infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ (281474976710656 * ε) * r) ∧
      closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
        P.orthogonalProjectionOnto '' (Set.range f ∩ closedBall p (r / 16)) := by
  let root := supportCellRoot μ R hR k z
  let P := (S root).direction
  let B := (17039360 * ε) / 63
  let : Nonempty (S root) := (hS root).1.to_subtype
  have hr0 := latticeRadius_pos R hR k
  have hheight (x : Ambient d) (hx : x ∈ Set.range f) :
      infDist x (S root : Set (Ambient d)) ≤ B * latticeRadius R k := by
    obtain ⟨u, rfl⟩ := hx
    have h := hmodel.2.2.2.1 0 u
    simp only [activeRegionParameterMap, id_eq, Nat.add_zero] at h
    exact (infDist_le_dist_of_mem u.property).trans (by rwa [dist_comm])
  obtain ⟨g, hg, _, hcoords, _⟩ := exists_affine_plane_disk_chart
    (S root) (hS root).1 (P.orthogonalProjectionOnto p) (r / 16)
  let j : closedBall (P.orthogonalProjectionOnto p) (r / 16) → S root :=
    fun u => ⟨g u, (hcoords u).1⟩
  let H := f ∘ j
  have hj : Continuous j := hg.continuous.subtype_mk _
  have hH : Continuous H := hmodel.1.comp hj
  have hRange : Set.range H ⊆ Set.range f := by rintro _ ⟨u, rfl⟩; exact ⟨j u, rfl⟩
  have hDisp (u) : dist (P.orthogonalProjectionOnto (H u)) u.val ≤ B * latticeRadius R k := by
    have h := hmodel.2.2.2.1 0 (j u)
    simp only [activeRegionParameterMap, id_eq, Nat.add_zero] at h
    change dist (g u) (H u) ≤ B * latticeRadius R k at h
    rw [← (hcoords u).2]
    have hpj := P.norm_starProjection_apply_le (H u - g u)
    rw [map_sub] at hpj
    exact hpj.trans (by rw [norm_sub_rev]; simpa only [dist_eq_norm] using! h)
  have hBudget : B * latticeRadius R k + B * latticeRadius R k ≤ r / 32 := by
    have hcoeff : 2 * ((17039360 * ε) / 63) * 2097152 ≤ 1 / 32 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hrlarge hε.le
    have hrr := mul_le_mul_of_nonneg_right hcoeff hr.le
    dsimp [B]
    nlinarith
  have hDispBudget : B * latticeRadius R k ≤ r / 32 := by
    have hB : 0 ≤ B := by dsimp [B]; positivity
    nlinarith [mul_nonneg hB hr0.le]
  have hProjected := continuous_chart_inner_projection_coverage (S root) (hS root).1
    (P.orthogonalProjectionOnto p) (r / 16) H hH (Set.range f) hRange p (r / 32)
    (B * latticeRadius R k) (B * latticeRadius R k) (B * latticeRadius R k) (by positivity)
    (by rw [dist_self]; linarith) hDisp
    (fun u => hheight (H u) (hRange ⟨u, rfl⟩)) (hheight p hp)
    hDispBudget hBudget
  rw [show 2 * (r / 32) = r / 16 by ring] at hProjected
  refine ⟨P, (hS root).2, ?_, hProjected⟩
  intro x hx
  have hparallel := infDist_parallel_plane_through_point_le (S root) p x
  change infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ _ at hparallel
  have hxheight := hheight x hx.1
  have hpheight := hheight p hp
  have hscaled := mul_le_mul_of_nonneg_left hrlarge hε.le
  dsimp [B] at hxheight hpheight
  nlinarith [mul_pos hε hr]

end

end RieszRectifiability

end OAI

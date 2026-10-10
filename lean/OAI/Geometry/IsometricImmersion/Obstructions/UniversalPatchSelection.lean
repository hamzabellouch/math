import OAI.Geometry.IsometricImmersion.Immersions.OrientedHeightPullback
import OAI.Geometry.IsometricImmersion.Obstructions.DiskBoundaryObstruction

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem rank_one_boundary_eventually_admissible_patches
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {b : Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hbU : b ∈ U) (n : ℕ) (hb : b ∈ frontier (accumulatingDisk n))
    (e : Ambient) (he : IsUnitNormalAt F e b)
    (hrank : (secondFundamental F e b).rank = 1) :
    ∃ R : OrientationLabel, ∃ centers : ℕ → Coord,
      (∀ k, centers k ∈ orientedExteriorCenters n k R) ∧
      Tendsto centers atTop (𝓝 b) ∧
      ∀ᶠ k in atTop,
        orientedClosedPatch n k R (centers k) ⊆ U ∧
        PatchAdmissibleHeight
          (affinePullbackMetric g (centers k) (orientedPatchScale n k R • R.val))
          (height (affinePullbackImmersion F (centers k)
            (orientedPatchScale n k R • R.val)) e) := by
  obtain ⟨R, V, hVo, hbV, hVU, hgood⟩ :=
    rank_one_height_has_oriented_neighborhood hg hF hU hbU e he hrank
  obtain ⟨centers, hcenters, ht, hpatches⟩ :=
    every_boundary_point_every_orientation_patch_neighborhoods n b hb R
  refine ⟨R, centers, hcenters, ht, ?_⟩
  filter_upwards [hpatches V (hVo.mem_nhds hbV)] with k hk
  exact ⟨hk.trans hVU,
    oriented_patch_height_admissible_of_subset hg hF hU e he.1 hVU R hgood
      n k (centers k) hk⟩

theorem rank_one_boundary_exists_admissible_patch
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {b : Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hbU : b ∈ U) (n : ℕ) (hb : b ∈ frontier (accumulatingDisk n))
    (e : Ambient) (he : IsUnitNormalAt F e b)
    (hrank : (secondFundamental F e b).rank = 1) (kmin : ℕ) :
    ∃ R : OrientationLabel, ∃ k ≥ kmin, ∃ c ∈ orientedExteriorCenters n k R,
      orientedClosedPatch n k R c ⊆ U ∧
      PatchAdmissibleHeight
        (affinePullbackMetric g c (orientedPatchScale n k R • R.val))
        (height (affinePullbackImmersion F c (orientedPatchScale n k R • R.val)) e) := by
  obtain ⟨R, centers, hcenters, _, hgood⟩ :=
    rank_one_boundary_eventually_admissible_patches hg hF hU hbU n hb e he hrank
  obtain ⟨k, hk⟩ := (hgood.and (eventually_ge_atTop kmin)).exists
  exact ⟨R, k, hk.2, centers k, hcenters k, hk.1.1, hk.1.2⟩

theorem immersion_containing_disk_has_admissible_patch
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (n : ℕ) (hDU : accumulatingDisk n ⊆ U)
    (hK : ∀ p ∈ roundOpenDisk (accumulatingCenter n) (accumulatingRadius n),
      gaussianCurvature g p < 0)
    (hKb : ∀ p ∈ frontier (accumulatingDisk n), gaussianCurvature g p = 0)
    (kmin : ℕ) :
    ∃ b ∈ frontier (accumulatingDisk n), ∃ e : Ambient,
      IsUnitNormalAt F e b ∧ secondFundamental F e b ≠ 0 ∧
      (secondFundamental F e b).rank = 1 ∧
      ∃ R : OrientationLabel, ∃ k ≥ kmin, ∃ c ∈ orientedExteriorCenters n k R,
        orientedClosedPatch n k R c ⊆ U ∧
        PatchAdmissibleHeight
          (affinePullbackMetric g c (orientedPatchScale n k R • R.val))
          (height (affinePullbackImmersion F c (orientedPatchScale n k R • R.val)) e) := by
  obtain ⟨b, hb, e, he, hne, hrank⟩ :=
    exists_roundDisk_boundary_unitNormal_rank_one hg hF hU (accumulatingRadius_pos n)
      hDU hK hKb
  have hbD : b ∈ accumulatingDisk n :=
    ((mem_frontier_roundClosedDisk_iff (accumulatingCenter n) b
      (accumulatingRadius_pos n)).mp hb).le
  refine ⟨b, hb, e, he, hne, hrank, ?_⟩
  exact rank_one_boundary_exists_admissible_patch hg hF hU (hDU hbD) n hb e he hrank kmin

theorem every_local_immersion_has_admissible_oriented_patch
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (h0 : (0 : Coord) ∈ U)
    (hK : ∀ n : ℕ, ∀ p ∈ roundOpenDisk (accumulatingCenter n) (accumulatingRadius n),
      gaussianCurvature g p < 0)
    (hKb : ∀ n : ℕ, ∀ p ∈ frontier (accumulatingDisk n), gaussianCurvature g p = 0)
    (nmin kmin : ℕ) :
    ∃ n ≥ nmin, ∃ b ∈ frontier (accumulatingDisk n), ∃ e : Ambient,
      IsUnitNormalAt F e b ∧ secondFundamental F e b ≠ 0 ∧
      (secondFundamental F e b).rank = 1 ∧
      ∃ R : OrientationLabel, ∃ k ≥ kmin, ∃ c ∈ orientedExteriorCenters n k R,
        orientedClosedPatch n k R c ⊆ U ∧
        PatchAdmissibleHeight
          (affinePullbackMetric g c (orientedPatchScale n k R • R.val))
          (height (affinePullbackImmersion F c (orientedPatchScale n k R • R.val)) e) := by
  have hdisks := eventually_accumulatingDisk_subset (hU.mem_nhds h0)
  obtain ⟨n, hn⟩ := (hdisks.and (eventually_ge_atTop nmin)).exists
  exact ⟨n, hn.2, immersion_containing_disk_has_admissible_patch hg hF hU n hn.1
    (hK n) (hKb n) kmin⟩

end SmoothLocal.Geometry

end

end OAI

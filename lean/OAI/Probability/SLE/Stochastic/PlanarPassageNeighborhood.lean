import OAI.Probability.SLE.Gauge.RibbonLimitPassageGeometry

namespace OAI

/-! Passage neighborhoods in the entire physical plane. Recentring a
physical ribbon does not preserve the upper half-plane, and this
construction uses only its embedded coordinate patch. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

/-- The actual limiting guide supplies a common physical neighborhood and
all varying-region conditions used by the retained-mass passage theorem. -/
theorem limiting_guide_passage_neighborhood_plane
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K : Set ℂ) (C L : ℝ≥0)
    (hC : 0 < C) (hL : 0 < L)
    (hupper : ∀ n, LipschitzOnWith C (Pₙ n) K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hP : ContinuousOn P K)
    (α : ℝ → ℂ) (hα : ContinuousOn α (Icc 0 2)) (x ε η : ℝ)
    (hx : |x| < ε) (hη : 0 < η)
    (hshape : EqOn α (fun t => P (guideCoordinate 0 x t)) (Icc 0 2))
    (hmem : ∀ t ∈ Icc (0 : ℝ) (3 / 2), guideCoordinate 0 x t ∈ interior K)
    (hbase : (1 : ℂ) ∈ K) :
    ∃ U : Set ℂ, IsOpen U ∧ α '' Icc (0 : ℝ) (3 / 2) ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ P '' interior K ∧
      ContinuousOn (longitudinalCoordinate P K 0) U ∧
      (∀ᶠ n in atTop, ContinuousOn (longitudinalCoordinate (Pₙ n) K 0) U) ∧
      TendstoLocallyUniformlyOn (fun n => longitudinalCoordinate (Pₙ n) K 0)
        (longitudinalCoordinate P K 0) atTop U ∧
      (∀ᶠ n in atTop, U ⊆ physicalPassageRegion (Pₙ n) K C ε η) ∧
      (∀ n z, z ∈ physicalPassageRegion (Pₙ n) K C ε η →
        longitudinalCoordinate (Pₙ n) K 0 z = 1 → ‖z - Pₙ n 1‖ < η / 4) ∧
      (∀ᶠ n in atTop,
        U ∩ {z | (1 / 3 : ℝ) < longitudinalCoordinate (Pₙ n) K 0 z ∧
          longitudinalCoordinate (Pₙ n) K 0 z < 2 / 3} ⊆ physicalMiddleRegion (Pₙ n) K 0 ε) := by
  let V := passageCoordinateRegion C ε η
  let A := α '' Icc (0 : ℝ) (3 / 2)
  have hA : IsCompact A := isCompact_Icc.image_of_continuousOn
    (hα.mono (Icc_subset_Icc_right (by norm_num)))
  have hAV : A ⊆ P '' (interior K ∩ V) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨guideCoordinate 0 x t, ⟨hmem t ht,
      guideCoordinate_mem_passageRegion C hC hx hη ht⟩,
      (hshape ⟨ht.1, ht.2.trans (by norm_num)⟩).symm⟩
  obtain ⟨U, hU, hAU, hUc, hUPV, hVlate, hKlate, _⟩ :=
    common_coordinate_region_neighborhood hpublished Pₙ P K A V L hL hP
      (fun n => (hupper n).continuousOn) hconv hlower hA
      (passageCoordinateRegion_isOpen C ε η) hAV
  have hUP : closure U ⊆ P '' interior K := hUPV.trans (image_mono inter_subset_left)
  have hlim := lower_lipschitz_uniform_limit Pₙ P K L hconv hlower
  have hi := lower_lipschitz_injOn P K L hlim
  have hwidth : ∀ z ∈ closure U, |(coordinateInverse P K z).im| < ε := by
    intro z hz
    obtain ⟨w, hw, he⟩ := hUPV hz
    rw [← he, coordinateInverse_left hi (interior_subset hw.1)]
    exact hw.2.2.2.1
  refine ⟨U, hU, hAU, hUc, hUP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (longitudinalCoordinate_continuousOn P K L 0 hlim).mono
      (subset_closure.trans (hUP.trans (image_mono interior_subset)))
  · filter_upwards [hKlate] with n hn
    exact (longitudinalCoordinate_continuousOn (Pₙ n) K L 0 (hlower n)).mono
      (subset_closure.trans (hn.trans (image_mono interior_subset)))
  · exact (longitudinalCoordinate_locally_uniform hpublished Pₙ P K L 0 hL hP
      (fun n => (hupper n).continuousOn) hconv hlower).mono (subset_closure.trans hUP)
  · exact hVlate.mono (fun _ hn => subset_closure.trans hn)
  · exact fun n z hz hp => physicalPassageRegion_terminal (Pₙ n) K C L ε η hC
      (hupper n) (hlower n) hbase hz hp
  · exact eventual_middle_region_inclusion Pₙ P K U L 0 ε hconv hlower hUc
      (hUP.trans (image_mono interior_subset))
      (hKlate.mono (fun _ hn => hn.trans (image_mono interior_subset))) hwidth

end SLEExactGauge.RibbonCoordinates

end

end OAI

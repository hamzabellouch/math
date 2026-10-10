import OAI.Probability.SLE.Geometry.WaypointRouteProbability

namespace OAI

/-! Uniform Brownian waypoint tube events stay initially in the surviving
domain, then avoid the complete access guide and hit the stopped past. -/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.RibbonCoordinates
open Target

theorem early_waypoint_coordinate_ball_safe
    (k side : ℝ) (hside : |side| = 1) {ε t : ℝ}
    (hk : 1 ≤ k) (hεsmall : ε ≤ 1 / 8) (ht : t ∈ Icc (0 : ℝ) 2) :
    ball (waypointRoute k side t) (1 / 32) ⊆
      futureRibbon k ∪ sideCorridor ε 1 ∪ sideCorridor (-1) (-ε) := by
  intro z hz
  have hn : ‖z - waypointRoute k side t‖ < 1 / 32 := by
    simpa only [mem_ball, dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z - waypointRoute k side t)).trans_lt hn
  have him := (Complex.abs_im_le_norm (z - waypointRoute k side t)).trans_lt hn
  rw [Complex.sub_re, waypointRoute_re] at hre
  rw [Complex.sub_im] at him
  have hr := abs_lt.mp hre
  have hi := abs_lt.mp him
  have hrouteim := abs_le.mp (waypointRoute_im_bound k side hside t)
  have hzim : |z.im| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  by_cases ht1 : t ≤ 1
  · left; left
    rw [unitClip_of_nonpos (by linarith : t - 1 ≤ 0)] at hr
    exact ⟨by linarith, hzim⟩
  · have hclip0 := unitClip_nonneg (t - 1)
    have hclip1 := unitClip_le_one (t - 1)
    have hzr : 0 < z.re := by linarith
    have hrouteabs : |(waypointRoute k side t).im| = 1 / 2 := by
      rw [waypointRoute_im, unitClip_of_one_le (by linarith : 1 ≤ t),
        unitClip_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0), abs_mul, hside]
      norm_num
    have hh : |(waypointRoute k side t).im| ≤
        |(waypointRoute k side t).im - z.im| + |z.im| := by
      simpa only [sub_add_cancel] using abs_add_le
        ((waypointRoute k side t).im - z.im) z.im
    rw [abs_sub_comm] at hh
    have hgap : ε < |z.im| := by linarith
    by_cases hz0 : 0 ≤ z.im
    · left; right
      exact ⟨hzr, by simpa only [abs_of_nonneg hz0] using hgap, (abs_lt.mp hzim).2⟩
    · right
      rw [abs_of_neg (lt_of_not_ge hz0)] at hgap
      exact ⟨hzr, (abs_lt.mp hzim).1, by linarith⟩

theorem physical_early_waypoint_tube_survives
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (K : ℝ≥0) (hK : 0 < (K : ℝ)) (γ : ℝ≥0 → ℂ) (T : ℝ≥0)
    {k ε side : ℝ} (hk : 1 ≤ k) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8)
    (hside : |side| = 1)
    (hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k ∧ |z.im| ≤ ε})
    (hunbounded : ¬ Bornology.IsBounded (P '' futureRibbon k))
    (hlower : ∀ u ∈ crossingPatch k, ∀ v ∈ crossingPatch k,
      dist u v ≤ K * dist (P u) (P v))
    (ζ : ℝ → ℂ)
    (hnear : ∀ t ∈ Icc (0 : ℝ) 2,
      dist (ζ t) (P (waypointRoute k side t)) < (1 / 32 : ℝ) / K) :
    MapsTo ζ (Icc 0 2) (survivingDomain γ T) := by
  have hk0 : 0 ≤ k := by linarith
  have hfuture := futureRibbon_survives P hP hi hk0 hH γ T
    (by rintro z ⟨u, hu, rfl⟩; obtain ⟨v, hv, he⟩ := hpast ⟨u, hu, rfl⟩;
        exact ⟨v, ⟨hv.1, hv.2.1⟩, he⟩) hunbounded
  have hupper := sideCorridor_survives P hP hi hH γ T hk0
    (show ε < 1 by linarith) (show -1 ≤ ε by linarith) le_rfl
    (fun x hx => hx.1.trans_le (le_abs_self x)) hpast hunbounded
  have hlowerSide := sideCorridor_survives P hP hi hH γ T hk0
    (show -1 < -ε by linarith) le_rfl (show -ε ≤ 1 by linarith)
    (fun x hx => (show ε < -x by linarith [hx.2]).trans_le (neg_le_abs x)) hpast hunbounded
  intro t ht
  have hpatch := waypointRoute_ball_subset_patch k side hside t
  have hsub := crossingPatch_subset_closedRibbon hk
  have hball := ball_subset_closedBall.trans (hpatch.trans hsub)
  obtain ⟨z, hz, he⟩ := ball_subset_image_ball P (waypointRoute k side t)
    (by norm_num : (0 : ℝ) < 1 / 32) hK (hP.mono (hpatch.trans hsub))
    (hpublished P _ _ (by norm_num) (hP.mono hball) (hi.mono hball))
    (fun z hz => hlower z (hpatch hz) _ (hpatch (mem_closedBall_self (by norm_num))))
    (hnear t ht)
  rw [← he]
  rcases early_waypoint_coordinate_ball_safe k side hside hk hεsmall ht hz with
    (hf | hu) | hl
  · exact hfuture (mem_image_of_mem P hf)
  · exact hupper (mem_image_of_mem P hu)
  · exact hlowerSide (mem_image_of_mem P hl)

/-- One positive probability gives the complete route geometry: the early
part survives, the later part avoids the full guide, and the final leg
hits the actual stopped past. No harmonic-measure labels are assumed. -/
theorem uniform_brownian_waypoint_passage_geometry
    (hopen : PublishedPlanarDiskOpenness) (hsupport : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W) (C K : ℝ≥0) (hK : 0 < (K : ℝ)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ P : ℂ → ℂ,
      ContinuousOn P closedRibbon → InjOn P closedRibbon →
      (∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane) →
      ∀ k ε x side : ℝ, 1 ≤ k → 0 < ε → ε ≤ 1 / 8 → |x| ≤ 1 / 16 →
      (side = -1 ∨ side = 1) → LipschitzOnWith C P (crossingPatch k) →
      (∀ u ∈ crossingPatch k, ∀ v ∈ crossingPatch k,
        dist u v ≤ K * dist (P u) (P v)) →
      ∀ (γ xp : ℝ≥0 → ℂ) (T : ℝ≥0), 0 < T →
      ContinuousOn xp (Icc 0 T) → EqOn γ (P ∘ xp) (Icc 0 T) →
      (xp 0).re = 0 → (xp T).re = k →
      MapsTo xp (Icc 0 T) closedRibbon →
      (∀ t ∈ Icc 0 T, (xp t).re ≤ k ∧ |(xp t).im| ≤ ε) →
      (¬ Bornology.IsBounded (P '' futureRibbon k)) →
      q ≤ (W.prod W) {b |
        let ζ := physicalUnitBrownianPath (P ((k + 1 / 2 : ℝ) : ℂ)) b
        MapsTo ζ (Icc 0 2) (survivingDomain γ T) ∧
        (∀ t ∈ Icc (1 / 4 : ℝ) 3, ∀ u : ℝ, 0 ≤ u → ζ t ≠ P (guideCoordinate k x u)) ∧
        ∃ s ∈ Icc 0 T, ∃ t ∈ Icc (0 : ℝ) 3, γ s = ζ t} := by
  obtain ⟨q, hq, hprob⟩ := uniform_physical_waypoint_tube_probability hsupport W hW C
    (div_pos (by norm_num : (0 : ℝ) < 1 / 32) hK)
  refine ⟨q, hq, ?_⟩
  intro P hP hi hH k ε x side hk hε hεsmall hx hside hL hlower γ xp T hT
    hxp hγ hxp0 hxpT hcoords hcore hunbounded
  have habs : |side| = 1 := by rcases hside with rfl | rfl <;> norm_num
  have hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k ∧ |z.im| ≤ ε} := by
    rintro z ⟨s, hs, rfl⟩
    exact ⟨xp s, ⟨hcoords hs, hcore s hs⟩, (hγ hs).symm⟩
  refine (hprob P k side habs hL).trans (measure_mono ?_)
  intro b hb
  let ζ := physicalUnitBrownianPath (P ((k + 1 / 2 : ℝ) : ℂ)) b
  refine ⟨physical_early_waypoint_tube_survives hopen P hP hi hH K hK γ T hk hε hεsmall
    habs hpast hunbounded hlower ζ (fun t ht => hb t ⟨ht.1, ht.2.trans (by norm_num)⟩), ?_, ?_⟩
  · intro t ht u hu he
    have hh := physical_waypointRoute_avoids_complete_guide hopen P hP hi K hK hk hx habs
      hlower ht.1 hu
    apply hh
    rw [← he]
    exact hb t ⟨by linarith [ht.1], ht.2⟩
  · let γr : ℝ → ℂ := fun s => γ s.toNNReal
    let xpr : ℝ → ℂ := fun s => xp s.toNNReal
    have hmap : MapsTo Real.toNNReal (Icc (0 : ℝ) T) (Icc 0 T) := by
      intro s hs
      exact ⟨bot_le, (Real.toNNReal_le_iff_le_coe).mpr hs.2⟩
    have hcont : ContinuousOn xpr (Icc (0 : ℝ) T) :=
      hxp.comp (by fun_prop) hmap
    obtain ⟨s, hs, t, ht, he⟩ := physical_waypoint_tube_hits_past hopen P hP hi K hK hk
      hε hεsmall (by exact_mod_cast hT : (0 : ℝ) < T) hside hlower γr xpr ζ hcont
      (fun s hs => hγ (hmap hs)) (by simpa [xpr] using hxp0)
      (by simpa [xpr] using hxpT) (fun s hs => (hcore _ (hmap hs)).2)
      (physicalUnitBrownianPath_continuous _ b).continuousOn hb
    exact ⟨s.toNNReal, hmap hs, t, ht, he⟩

end SLEExactGauge.RibbonCoordinates

end

end OAI

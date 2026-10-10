import OAI.Probability.SLE.Gauge.RibbonFrontFreshness

namespace OAI

/-! The physical ribbon guide supplies surviving-domain and compactness
geometry under a two-sided waypoint angle hypothesis. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

theorem ribbon_access_guide_geometry
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (hescape : Tendsto (fun s : ℝ => ‖P (s : ℂ)‖) atTop atTop)
    (γ xp : ℝ≥0 → ℂ) (T : ℝ≥0) (hxp : ContinuousOn xp (Icc 0 T))
    (hxp0 : (xp 0).re = 0) (hcoords : MapsTo xp (Icc 0 T) closedRibbon)
    (hγ : EqOn γ (P ∘ xp) (Icc 0 T))
    (k x : ℝ) (hk : 0 ≤ k) (hx : |x| ≤ 1 / 4)
    (htip : xp T = (k : ℂ) + (x : ℂ) * Complex.I)
    (hfront : ∀ t : ℝ≥0, t < T → (xp t).re < k)
    (C : ℝ≥0) (K : ℝ) (hK : 0 < K)
    (hL : LipschitzOnWith C P (guidePatch k))
    (hlower : ∀ u ∈ guidePatch k, ∀ v ∈ guidePatch k,
      dist u v ≤ K * dist (P u) (P v)) :
    let α := fun t => P (guideCoordinate k x t)
    ContinuousOn α (Icc 0 2) ∧ InjOn α (Icc 0 2) ∧ α 0 = γ T ∧
      MapsTo α (Ioc 0 2) (survivingDomain γ T) ∧
      (∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s) ∧
      LipschitzOnWith (2 * C) α (Icc 0 2) ∧
      (∀ u ∈ Icc (0 : ℝ) 2, ∀ v ∈ Icc (0 : ℝ) 2,
        (1 / K) * |u - v| ≤ dist (α u) (α v)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ r : ℝ, 0 < r ∧
        ∀ t ∈ Icc δ 2, ball (α t) r ⊆ survivingDomain γ T) := by
  dsimp only
  have htipre : (xp T).re = k := by simp [htip]
  have htipim : (xp T).im = x := by simp [htip]
  have hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k} := by
    rintro z ⟨t, ht, rfl⟩
    refine ⟨xp t, ⟨hcoords ht, ?_⟩, (hγ ht).symm⟩
    by_cases he : t = T
    · simpa only [he, htipre] using le_rfl (a := k)
    · exact (hfront t (lt_of_le_of_ne ht.2 he)).le
  have hunbounded := futureRibbon_unbounded_of_centerline_escape P k hescape
  have hguidePatch : MapsTo (guideCoordinate k x) (Icc (0 : ℝ) 2) (guidePatch k) :=
    fun _ ht => guideCoordinate_mem_patch hx ht
  have hguideClosed := hguidePatch.mono_right (guidePatch_subset_closedRibbon hk)
  have hαcont : ContinuousOn (fun t => P (guideCoordinate k x t)) (Icc 0 2) :=
    hP.comp (guideCoordinate_continuous k x).continuousOn hguideClosed
  have hαinj : InjOn (fun t => P (guideCoordinate k x t)) (Icc 0 2) := by
    intro u hu v hv he
    have hc := hi (hguideClosed hu) (hguideClosed hv) he
    have hre := congrArg Complex.re hc
    simp only [guideCoordinate_re] at hre
    linarith
  have hα0 : P (guideCoordinate k x 0) = γ T := by
    rw [guideCoordinate_zero, ← htip]
    exact (hγ ⟨bot_le, le_rfl⟩).symm
  have hαD : MapsTo (fun t => P (guideCoordinate k x t)) (Ioc 0 2)
      (survivingDomain γ T) := by
    intro t ht
    apply futureRibbon_survives P hP hi hk hH γ T hpast hunbounded
    apply mem_image_of_mem
    change k < (guideCoordinate k x t).re ∧ |(guideCoordinate k x t).im| < 1
    exact ⟨by rw [guideCoordinate_re]; linarith [ht.1],
      (guideCoordinate_im_bound ht.1.le).trans_lt (hx.trans_lt (by norm_num))⟩
  have hfresh := ribbon_front_tip_survives_prior P hP hi hH hescape γ xp T hxp hxp0 hcoords hγ
    (fun t ht => by rw [htipre]; exact hfront t ht)
    (by rw [htipim]; exact hx.trans_lt (by norm_num))
  exact ⟨hαcont, hαinj, hα0, hαD, hfresh, physical_guide_lipschitz P C hx hL,
    physical_guide_lower_chord P hx hK hlower,
    fun δ hδ hδ2 => physical_guide_clearance_away hpublished P hP hi hk hx hK
      hH γ T hpast hunbounded hlower hδ hδ2⟩

end SLEExactGauge.RibbonCoordinates

end

end OAI

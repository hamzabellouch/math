import OAI.Probability.SLE.Geometry.WaypointCrosscutSides

namespace OAI

/-! Pointwise geometry of either physical Brownian tube, retaining
its chosen side for the conformal exit-arc law. -/

noncomputable section
open Set Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

theorem physical_waypoint_tube_geometry
    (hopen : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (K : ℝ≥0) (hK : 0 < (K : ℝ)) {k ε x side : ℝ}
    (hk : 1 ≤ k) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) (hx : |x| ≤ 1 / 16)
    (hside : side = -1 ∨ side = 1)
    (hlower : ∀ u ∈ crossingPatch k, ∀ v ∈ crossingPatch k,
      dist u v ≤ K * dist (P u) (P v))
    (γ xp : ℝ≥0 → ℂ) (T : ℝ≥0) (hT : 0 < T)
    (hxp : ContinuousOn xp (Icc 0 T)) (hγ : EqOn γ (P ∘ xp) (Icc 0 T))
    (hxp0 : (xp 0).re = 0) (hxpT : (xp T).re = k)
    (hcoords : MapsTo xp (Icc 0 T) closedRibbon)
    (hcore : ∀ t ∈ Icc 0 T, (xp t).re ≤ k ∧ |(xp t).im| ≤ ε)
    (hunbounded : ¬ Bornology.IsBounded (P '' futureRibbon k))
    (ζ : ℝ → ℂ) (hζ : Continuous ζ)
    (hnear : ∀ t ∈ Icc (0 : ℝ) 3,
      dist (ζ t) (P (waypointRoute k side t)) < (1 / 32 : ℝ) / K) :
    MapsTo ζ (Icc 0 2) (survivingDomain γ T) ∧
      (∀ t ∈ Icc (1 / 4 : ℝ) 3, ∀ u : ℝ, 0 ≤ u →
        ζ t ≠ P (guideCoordinate k x u)) ∧
      ∃ s ∈ Icc 0 T, ∃ t ∈ Icc (0 : ℝ) 3, γ s = ζ t := by
  have habs : |side| = 1 := by rcases hside with rfl | rfl <;> norm_num
  have hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k ∧ |z.im| ≤ ε} := by
    rintro z ⟨s, hs, rfl⟩
    exact ⟨xp s, ⟨hcoords hs, hcore s hs⟩, (hγ hs).symm⟩
  refine ⟨physical_early_waypoint_tube_survives hopen P hP hi hH K hK γ T hk hε hεsmall
    habs hpast hunbounded hlower ζ (fun t ht => hnear t ⟨ht.1, ht.2.trans (by norm_num)⟩), ?_, ?_⟩
  · intro t ht u hu he
    have hh := physical_waypointRoute_avoids_complete_guide hopen P hP hi K hK hk hx habs
      hlower ht.1 hu
    apply hh
    rw [← he]
    exact hnear t ⟨by linarith [ht.1], ht.2⟩
  · let γr : ℝ → ℂ := fun s => γ s.toNNReal
    let xpr : ℝ → ℂ := fun s => xp s.toNNReal
    have hmap : MapsTo Real.toNNReal (Icc (0 : ℝ) T) (Icc 0 T) := by
      intro s hs
      exact ⟨bot_le, (Real.toNNReal_le_iff_le_coe).mpr hs.2⟩
    have hcont : ContinuousOn xpr (Icc (0 : ℝ) T) := hxp.comp (by fun_prop) hmap
    obtain ⟨s, hs, t, ht, he⟩ := physical_waypoint_tube_hits_past hopen P hP hi K hK hk
      hε hεsmall (by exact_mod_cast hT : (0 : ℝ) < T) hside hlower γr xpr ζ hcont
      (fun s hs => hγ (hmap hs)) (by simpa [xpr] using hxp0)
      (by simpa [xpr] using hxpT) (fun s hs => (hcore _ (hmap hs)).2)
      hζ.continuousOn hnear
    exact ⟨s.toNNReal, hmap hs, t, ht, he⟩

end SLEExactGauge.RibbonCoordinates

end

end OAI

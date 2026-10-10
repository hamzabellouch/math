import OAI.Probability.SLE.Geometry.WaypointTubeGeometry
import OAI.Probability.SLE.Geometry.CrosscutExitSides
import OAI.Probability.SLE.Geometry.WaypointAngleNumerics

namespace OAI

/-! The actual two-sided physical route events bound the two half-plane
exit arcs from below.  Uniform route support is proved elsewhere; only the
generic published conformal Brownian exit law is parameterized here. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.RibbonCoordinates
open Target CrosscutSides

theorem finite_exit_event_measure_le_arc
    (μ : Measure (Driver × Driver)) (D : Set ℂ) (g : ℂ → ℂ) (w : ℂ)
    (h : ℂ ≃ₜ ℂ) (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (hg : ContinuousOn g D) (E : Set (Driver × Driver)) {dir : ℝ}
    (hdir : dir = -1 ∨ dir = 1)
    (hexit : ∀ᵐ b ∂μ, ∀ τ : ℝ, UnitWindowFirstExit D (physicalUnitBrownianPath w b) τ →
      ∃ x : ℝ, x ≠ 0 ∧ Tendsto (fun t => g (physicalUnitBrownianPath w b t))
        (𝓝[<] τ) (𝓝 (x : ℂ)))
    (hgeom : ∀ b ∈ E, ∃ τ : ℝ,
      UnitWindowFirstExit D (physicalUnitBrownianPath w b) τ ∧ (1 / 4 : ℝ) < τ ∧
      ∀ t ∈ Ico (1 / 4 : ℝ) τ, (h (g (physicalUnitBrownianPath w b t))).re ≠ 0)
    (hstart : ∀ b ∈ E, 0 < dir * (h (g (physicalUnitBrownianPath w b (1 / 4)))).re) :
    μ E ≤ μ (unitWindowExitArc D g w dir) := by
  apply measure_mono_ae
  filter_upwards [hexit] with b hb
  intro he
  obtain ⟨τ, hτ, haτ, hn⟩ := hgeom b he
  obtain ⟨x, hx, hlim⟩ := hb τ hτ
  refine ⟨τ, hτ, x, ?_, hlim⟩
  have hs := hstart b he
  rcases hdir with rfl | rfl
  · have hxneg := negative_first_exit_belongs_to_arc D g h hreal hg
      (physicalUnitBrownianPath w b) (physicalUnitBrownianPath_continuous w b)
      hτ haτ hn (by nlinarith) x hx hlim
    nlinarith
  · have hxpos := positive_first_exit_belongs_to_arc D g h hreal hg
      (physicalUnitBrownianPath w b) (physicalUnitBrownianPath_continuous w b)
      hτ haτ hn (by simpa using hs) x hx hlim
    simpa using hxpos

theorem ribbon_tube_harmonic_bounds
    (hopen : PublishedPlanarDiskOpenness) (hexitLaw : PublishedHalfPlaneConformalExitLaw)
    (W : WienerLaw) (hW : IsWiener W) (K : ℝ≥0) (hK : 0 < (K : ℝ))
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    {k ε x : ℝ} (hk : 1 ≤ k) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8)
    (hx : |x| ≤ 1 / 16)
    (hlower : ∀ u ∈ crossingPatch k, ∀ v ∈ crossingPatch k,
      dist u v ≤ K * dist (P u) (P v))
    (γ xp : ℝ≥0 → ℂ) (hγc : Continuous γ) (T : ℝ≥0) (hT : 0 < T)
    (hxp : ContinuousOn xp (Icc 0 T)) (hγ : EqOn γ (P ∘ xp) (Icc 0 T))
    (hxp0 : (xp 0).re = 0) (hxpT : (xp T).re = k)
    (hcoords : MapsTo xp (Icc 0 T) closedRibbon)
    (hcore : ∀ t ∈ Icc 0 T, (xp t).re ≤ k ∧ |(xp t).im| ≤ ε)
    (hunbounded : ¬ Bornology.IsBounded (P '' futureRibbon k))
    (g F : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (survivingDomain γ T))
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hgH : MapsTo g (survivingDomain γ T) upperHalfPlane)
    (hFD : MapsTo F upperHalfPlane (survivingDomain γ T))
    (hFg : ∀ z ∈ survivingDomain γ T, F (g z) = z)
    (hgF : ∀ z ∈ upperHalfPlane, g (F z) = z)
    (h : ℂ ≃ₜ ℂ) (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (hcut : ∀ z ∈ survivingDomain γ T, (h (g z)).re = 0 →
      ∃ u : ℝ, 0 ≤ u ∧ P (guideCoordinate k x u) = z)
    (hloc : ContinuousOn (fun z => h (g (P z)))
      (ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)))
    (hloci : InjOn (fun z => h (g (P z)))
      (ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)))
    (hlocz : ∀ z ∈ ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4),
      (h (g (P z))).re = 0 ↔ z.im = 0)
    (q : ℝ≥0∞)
    (hprob : ∀ side : ℝ, (side = -1 ∨ side = 1) →
      q ≤ (W.prod W) {b | ∀ t ∈ Icc (0 : ℝ) 3,
        dist (physicalUnitBrownianPath (P ((k + 1 / 2 : ℝ) : ℂ)) b t)
          (P (waypointRoute k side t)) < (1 / 32 : ℝ) / K}) :
    q ≤ ENNReal.ofReal ((g (P ((k + 1 / 2 : ℝ) : ℂ))).arg / Real.pi) ∧
      q ≤ ENNReal.ofReal (1 - (g (P ((k + 1 / 2 : ℝ) : ℂ))).arg / Real.pi) := by
  let D := survivingDomain γ T
  let w := P ((k + 1 / 2 : ℝ) : ℂ)
  let E := fun side : ℝ => {b | ∀ t ∈ Icc (0 : ℝ) 3,
    dist (physicalUnitBrownianPath w b t) (P (waypointRoute k side t)) < (1 / 32 : ℝ) / K}
  have hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k} := by
    rintro z ⟨s, hs, rfl⟩
    exact ⟨xp s, ⟨hcoords hs, (hcore s hs).1⟩, (hγ hs).symm⟩
  have hwD : w ∈ D := by
    apply futureRibbon_survives P hP hi (by linarith) hH γ T hpast hunbounded
    exact ⟨((k + 1 / 2 : ℝ) : ℂ), ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨hae, hnegBound, hposBound⟩ := hexitLaw W hW D g F
    (isOpen_survivingDomain hγc T) (fun z hz => hz.1.1) hg hF hgH hFD hFg hgF w hwD
  obtain ⟨side, hside, hpos, hneg⟩ := physical_waypoint_tubes_opposite_sides hopen P hP hi
    K hK hk hlower (fun z => h (g (P z))) (fun z => (h (g z)).re)
    hloc hloci hlocz (fun _ _ => rfl)
  have hgeom (side' : ℝ) (hside' : side' = -1 ∨ side' = 1) (b : Driver × Driver)
      (hb : b ∈ E side') : ∃ τ : ℝ,
      UnitWindowFirstExit D (physicalUnitBrownianPath w b) τ ∧ (1 / 4 : ℝ) < τ ∧
      ∀ t ∈ Ico (1 / 4 : ℝ) τ, (h (g (physicalUnitBrownianPath w b t))).re ≠ 0 := by
    let ζ := physicalUnitBrownianPath w b
    have hζ : Continuous ζ := physicalUnitBrownianPath_continuous w b
    obtain ⟨hearly, havoid, hhit⟩ := physical_waypoint_tube_geometry hopen P hP hi hH K hK
      hk hε hεsmall hx hside' hlower γ xp T hT hxp hγ hxp0 hxpT hcoords hcore hunbounded
      ζ hζ hb
    obtain ⟨τ, hτ, hout, hin⟩ := waypoint_first_exit_after_early_prefix γ hγc T ζ
      hζ.continuousOn hearly hhit
    refine ⟨τ, ⟨⟨by linarith [hτ.1], hτ.2⟩, hout, hin⟩, by linarith [hτ.1], ?_⟩
    intro t ht he
    obtain ⟨u, hu, heq⟩ := hcut (ζ t) (hin ⟨by linarith [ht.1], ht.2⟩) he
    exact havoid t ⟨ht.1, ht.2.le.trans hτ.2⟩ u hu heq.symm
  have hposProb : q ≤ (W.prod W) (unitWindowExitArc D g w 1) := by
    refine (hprob side hside).trans (finite_exit_event_measure_le_arc (W.prod W) D g w h hreal
      hg.continuousOn (E side) (Or.inr rfl) hae (hgeom side hside) ?_)
    intro b hb
    simpa only [one_mul] using hpos _ (hb _ (by norm_num))
  have hsideNeg : -side = -1 ∨ -side = 1 := by
    rcases hside with rfl | rfl <;> norm_num
  have hnegProb : q ≤ (W.prod W) (unitWindowExitArc D g w (-1)) := by
    refine (hprob (-side) hsideNeg).trans (finite_exit_event_measure_le_arc (W.prod W) D g w h hreal
      hg.continuousOn (E (-side)) (Or.inl rfl) hae (hgeom (-side) hsideNeg) ?_)
    intro b hb
    have hh := hneg _ (hb _ (by norm_num))
    nlinarith
  exact ⟨hnegProb.trans hnegBound, hposProb.trans hposBound⟩

end SLEExactGauge.RibbonCoordinates

end

end OAI

import OAI.Probability.SLE.Geometry.WaypointRouteAvoidance
import OAI.Probability.SLE.Geometry.PublishedWienerSupport

namespace OAI

/-! Uniform positive probabilities for physical waypoint-route tubes.
Their constants depend only on the patch speed and tube radius. -/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction

namespace SLEExactGauge.RibbonCoordinates
open Target RectangleCrossing

def basedPhysicalWaypointRoute (P : ℂ → ℂ) (k side : ℝ)
    (hP : ContinuousOn P (crossingPatch k)) (hside : |side| = 1) : unitInterval →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => P (waypointRoute k side (3 * (t : ℝ))) - P ((k + 1 / 2 : ℝ) : ℂ),
      (hP.comp ((waypointRoute_continuous k side).comp (by fun_prop)).continuousOn
        (fun t _ => waypointRoute_mem_patch k side hside _)).sub continuousOn_const |>.domRestrict⟩

theorem basedPhysicalWaypointRoute_zero
    (P : ℂ → ℂ) (k side : ℝ)
    (hP : ContinuousOn P (crossingPatch k)) (hside : |side| = 1) :
    basedPhysicalWaypointRoute P k side hP hside 0 = 0 := by
  change P (waypointRoute k side (3 * (0 : ℝ))) - P ((k + 1 / 2 : ℝ) : ℂ) = 0
  rw [mul_zero, waypointRoute_zero, sub_self]

theorem basedPhysicalWaypointRoute_lipschitz
    (P : ℂ → ℂ) (k side : ℝ) (hside : |side| = 1) (C : ℝ≥0)
    (hP : LipschitzOnWith C P (crossingPatch k)) :
    LipschitzWith (9 * C) (basedPhysicalWaypointRoute P k side hP.continuousOn hside) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hh := hP.dist_le_mul (waypointRoute k side (3 * (u : ℝ)))
    (waypointRoute_mem_patch k side hside _)
    (waypointRoute k side (3 * (v : ℝ))) (waypointRoute_mem_patch k side hside _)
  have hr := (waypointRoute_lipschitz k side hside).dist_le_mul
    (3 * (u : ℝ)) (3 * (v : ℝ))
  have hd : dist (3 * (u : ℝ)) (3 * (v : ℝ)) = 3 * dist u v := by
    rw [Subtype.dist_eq, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    norm_num
  rw [hd] at hr
  have hp := hh.trans (mul_le_mul_of_nonneg_left hr C.coe_nonneg)
  change dist (P (waypointRoute k side (3 * (u : ℝ))) - P ((k + 1 / 2 : ℝ) : ℂ))
    (P (waypointRoute k side (3 * (v : ℝ))) - P ((k + 1 / 2 : ℝ) : ℂ)) ≤ _
  rw [dist_sub_right]
  convert hp using 1
  push_cast
  ring

def unitClipPoint (t : ℝ) : unitInterval :=
  ⟨unitClip t, unitClip_nonneg t, unitClip_le_one t⟩

theorem continuous_unitClipPoint : Continuous unitClipPoint :=
  unitClip_lipschitz.continuous.subtype_mk _

def physicalUnitBrownianPath (a : ℂ) (b : Driver × Driver) (t : ℝ) : ℂ :=
  a + planarUnitPath b (unitClipPoint (t / 3))

theorem physicalUnitBrownianPath_continuous (a : ℂ) (b : Driver × Driver) :
    Continuous (physicalUnitBrownianPath a b) := by
  exact continuous_const.add ((planarUnitPath b).continuous.comp
    (continuous_unitClipPoint.comp (by fun_prop)))

/-- Pointwise Brownian support gives a single positive probability for
every physical route with the fixed patch speed bound. -/
theorem uniform_physical_waypoint_tube_probability
    (hpublished : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W) (C : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ P : ℂ → ℂ, ∀ k side : ℝ, |side| = 1 →
      LipschitzOnWith C P (crossingPatch k) → q ≤ (W.prod W) {b |
        ∀ t ∈ Icc (0 : ℝ) 3,
          dist (physicalUnitBrownianPath (P ((k + 1 / 2 : ℝ) : ℂ)) b t)
            (P (waypointRoute k side t)) < ε} := by
  obtain ⟨q, hq, hbound⟩ := uniform_planarWiener_tube_probability hpublished W hW (9 * C) hε
  refine ⟨q, hq, ?_⟩
  intro P k side hside hP
  refine (hbound (basedPhysicalWaypointRoute P k side hP.continuousOn hside)
    (basedPhysicalWaypointRoute_lipschitz P k side hside C hP)
    (basedPhysicalWaypointRoute_zero P k side hP.continuousOn hside)).trans (measure_mono ?_)
  intro b hb t ht
  let u : unitInterval := ⟨t / 3, by linarith [ht.1], by linarith [ht.2]⟩
  have hu : unitClipPoint (t / 3) = u := Subtype.ext (unitClip_of_mem u.property)
  have he : 3 * (u : ℝ) = t := by dsimp [u]; ring
  have hh := hb u
  change dist (planarUnitPath b u)
    (P (waypointRoute k side (3 * (u : ℝ))) - P ((k + 1 / 2 : ℝ) : ℂ)) < ε at hh
  rw [he] at hh
  unfold physicalUnitBrownianPath
  rw [hu]
  rw [dist_eq_norm] at hh ⊢
  convert hh using 1
  congr 1
  ring

/-- Either orientation of the final physical leg forces a hit of the
actual stopped past. -/
theorem physical_waypoint_tube_hits_past
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (K : ℝ≥0) (hK : 0 < (K : ℝ)) {k ε T side : ℝ}
    (hk : 1 ≤ k) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) (hT : 0 < T)
    (hside : side = -1 ∨ side = 1)
    (hlower : ∀ u ∈ crossingPatch k, ∀ v ∈ crossingPatch k,
      dist u v ≤ K * dist (P u) (P v))
    (γ xp ζ : ℝ → ℂ) (hxp : ContinuousOn xp (Icc 0 T))
    (hγ : EqOn γ (P ∘ xp) (Icc 0 T))
    (hxp0 : (xp 0).re = 0) (hxpT : (xp T).re = k)
    (hcore : ∀ t ∈ Icc (0 : ℝ) T, |(xp t).im| ≤ ε)
    (hζ : ContinuousOn ζ (Icc 0 3))
    (hnear : ∀ t ∈ Icc (0 : ℝ) 3,
      dist (ζ t) (P (waypointRoute k side t)) < (1 / 32 : ℝ) / K) :
    ∃ s ∈ Icc (0 : ℝ) T, ∃ t ∈ Icc (0 : ℝ) 3, γ s = ζ t := by
  have hrad : (1 / 32 : ℝ) / K ≤ (1 / 8 : ℝ) / K :=
    div_le_div_of_nonneg_right (by norm_num) hK.le
  rcases hside with rfl | rfl
  · have hmap : MapsTo (fun t : ℝ => 2 + t) (Icc 0 1) (Icc 0 3) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    obtain ⟨s, hs, t, ht, he⟩ := physical_transverse_tube_hits_past hpublished P hP hi K hK
      hk hε hεsmall hT hlower γ xp (fun t => ζ (2 + t)) hxp hγ hxp0 hxpT hcore
      (hζ.comp (by fun_prop) hmap) (fun t ht => by
        have hh := (hnear _ (hmap ht)).trans_le hrad
        rwa [waypointRoute_final_negative k ht] at hh)
    exact ⟨s, hs, 2 + t, hmap ht, he⟩
  · have hmap : MapsTo (fun t : ℝ => 3 - t) (Icc 0 1) (Icc 0 3) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    obtain ⟨s, hs, t, ht, he⟩ := physical_transverse_tube_hits_past hpublished P hP hi K hK
      hk hε hεsmall hT hlower γ xp (fun t => ζ (3 - t)) hxp hγ hxp0 hxpT hcore
      (hζ.comp (by fun_prop) hmap) (fun t ht => by
        have hh := (hnear _ (hmap ht)).trans_le hrad
        rwa [waypointRoute_final_positive k ht] at hh)
    exact ⟨s, hs, 3 - t, hmap ht, he⟩

end SLEExactGauge.RibbonCoordinates

end

end OAI

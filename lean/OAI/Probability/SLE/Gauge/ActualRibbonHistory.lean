import OAI.Probability.SLE.Gauge.RibbonFrontStops

namespace OAI

/-! Construct the history required by the uniform passage theorem from
an actual global first-front event and physical prefix containment. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage

theorem actual_history_at_global_front
    {C L : ℝ≥0} {ε : ℝ}
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (P : ℂ → ℂ)
    (hemb : Topology.IsClosedEmbedding (fun z : closedRibbon => P z))
    (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (hescape : Tendsto (fun t : ℝ => ‖P (t : ℂ)‖) atTop atTop)
    (g : C(ℂ, ℝ)) (hg : ∀ z ∈ closedRibbon, g (P z) = z.re)
    (hg0 : g (γ 0) = 0) (k : ℝ) (hk : 1 ≤ k) (T : ℝ≥0)
    (hfirst : firstFrontTime (fun t => g (γ t)) k = (T : WithTop ℝ≥0))
    (hpast : MapsTo γ (Icc 0 T) (P '' {z ∈ closedRibbon | |z.im| ≤ ε}))
    (hoffset : |(coordinateInverse P closedRibbon (γ T)).im| ≤ ε / 4)
    (hupper : LipschitzOnWith C P (ribbonStepPatch k))
    (hlower : ∀ z ∈ ribbonStepPatch k, ∀ w ∈ ribbonStepPatch k,
      dist z w ≤ L * dist (P z) (P w)) :
    ∃ d : RibbonHistory C L ε, d.U = U ∧ d.trace = γ ∧ d.forward = G ∧
      d.inverse = F ∧ d.chart = P ∧ d.front = k ∧ d.time = T := by
  have hhit := FrontSuccessMeasurability.firstFrontTime_attained
    (fun t => g (γ t)) (g.continuous.comp hw.1) k T hfirst
  let xp := fun t => coordinateInverse P closedRibbon (γ t)
  have hmap : MapsTo γ (Icc 0 T) (P '' closedRibbon) :=
    fun _ ht => image_mono inter_subset_left (hpast ht)
  have hcoords : MapsTo xp (Icc 0 T) closedRibbon :=
    fun _ ht => coordinateInverse_mem (hmap ht)
  have hxpc : ContinuousOn xp (Icc 0 T) :=
    (coordinateInverse_continuousOn_of_embedding P hemb.isEmbedding).comp
      hw.1.continuousOn hmap
  have hγeq : EqOn γ (P ∘ xp) (Icc 0 T) :=
    fun _ ht => (coordinateInverse_right (hmap ht)).symm
  have hgtrace (t : ℝ≥0) (ht : t ∈ Icc 0 T) : g (γ t) = (xp t).re := by
    rw [hγeq ht]
    exact hg _ (hcoords ht)
  have hT : 0 < T := by
    apply lt_of_le_of_ne bot_le
    intro he
    have hh := hhit
    rw [← he] at hh
    change g (γ 0) = k at hh
    rw [hg0] at hh
    linarith
  have hxpre : (xp T).re = k := (hgtrace T ⟨bot_le, le_rfl⟩).symm.trans hhit
  have hattain : xp T = (k : ℂ) + ((xp T).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hxpre]
  have hstrict : ∀ t : ℝ≥0, t < T → (xp t).re < k := by
    have hh := strict_before_attained_front (fun t => g (γ t)) k T
      (g.continuous.comp hw.1).continuousOn (by rw [hg0]; linarith) hfirst
    intro t ht
    rw [← hgtrace t ⟨bot_le, ht.le⟩]
    exact hh t ht
  have hcore : ∀ t ∈ Icc 0 T, (xp t).re ≤ k ∧ |(xp t).im| ≤ ε := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rcases ht.2.eq_or_lt with rfl | hlt
      · exact hxpre.le
      · exact (hstrict t hlt).le
    · obtain ⟨z, ⟨hz, hiε⟩, he⟩ := hpast ht
      simpa only [xp, ← he, coordinateInverse_left hi hz] using hiε
  let d : RibbonHistory C L ε := {
    U := U
    trace := γ
    forward := G
    inverse := F
    driver_continuous := hU
    witness := hw
    chart := P
    chart_continuous := hP
    chart_injective := hi
    chart_upper := hH
    chart_escape := hescape
    front := k
    offset := (xp T).im
    front_ge_one := hk
    offset_bound := hoffset
    patch_upper := hupper
    patch_lower := hlower
    time := T
    time_pos := hT
    coordinates := xp
    coordinates_continuous := hxpc
    trace_coordinates := hγeq
    initial_front := by rw [← hgtrace 0 ⟨bot_le, bot_le⟩, hg0]
    attained := hattain
    coordinates_ribbon := hcoords
    past_core := hcore
    strict_past := hstrict }
  exact ⟨d, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SLEExactGauge

end

end OAI

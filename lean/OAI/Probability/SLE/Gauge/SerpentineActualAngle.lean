import OAI.Probability.SLE.Gauge.SerpentineActualGuide
import OAI.Probability.SLE.Geometry.GoodPrefixCoordinates
import OAI.Probability.SLE.Geometry.MarkedAccessAngle

namespace OAI

/-! Successful actual serpentine completion gives the marked-point angle
uniformly in the number of retained strips and in the trace history. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates FirstFrontPassage Target

theorem uniform_serpentine_actual_angle_nonneg
    (hopen : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hsupport : PublishedPlanarWienerUnitSupport) (W : WienerLaw) (hW : IsWiener W)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
      (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F → Continuous U →
      ∀ w : ℂ, ‖w‖ ≤ 1 → s ≤ w.im → 0 ≤ w.re →
      ∀ m : ℕ, 0 < m → ∀ g : C(ℂ, ℝ),
      (∀ z ∈ closedRibbon, g (physicalFitChart s w m z) = z.re) →
      ∀ ε : ℝ, ε ≤ 1 / 8 →
      () ∈ GoodRibbonPrefix (fun _ : Unit => γ)
        (fun _ => firstFrontTime (fun t => g (γ t)) (fitCompletion s w m))
        (physicalFitChart s w m) ε →
      let T := (firstFrontTime (fun t => g (γ t)) (fitCompletion s w m)).untopD 0
      s₀ ≤ (G T w - (U T : ℂ)).im / ‖G T w - (U T : ℂ)‖ := by
  obtain ⟨s₀, hs₀, hangle⟩ := uniform_marked_access_angle hopen hstraight hexit hsupport W hW
    (show 0 < s / 20 by positivity) (show s / 20 ≤ 1 by linarith)
  refine ⟨s₀, hs₀, ?_⟩
  intro U γ G F hw hU w hwn hwy hwr m hm g hg ε hε hpref
  have hchart : physicalExperimentChart s w m = physicalFitChart s w m := by
    funext z
    simp only [physicalExperimentChart, ite_eq_left hwr]
  have hemb : Topology.IsClosedEmbedding (fun z : closedRibbon => physicalFitChart s w m z) := by
    simpa only [hchart] using physicalExperimentChart_closedEmbedding hs w hwy hm
  obtain ⟨hP, hi, hH, hescape⟩ := physicalFitChart_geometry hs w hwy hm
  have hg0 : g (γ 0) = 0 := by
    rw [hw.2.1, ← physicalFitChart_zero hs w hwy hm]
    exact hg 0 (by simp [closedRibbon])
  have hk : 0 < (fitCompletion s w m : ℝ) := by
    have hbound := (fitCompletion_bounds hs w hwy hm).1
    have hEntry : 0 ≤ fitEntry s w m :=
      (by unfold fitHeight; positivity : (0 : ℝ) ≤ fitHeight m).trans (fit_entry_lower hs w hwy hm)
    have hcol : 0 ≤ columnEntry 0 m (2 * m) := columnEntry_nonneg le_rfl _ _
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    linarith
  obtain ⟨T, x, xp, hfirst, hT, hx, hxpc, hγeq, hxp0, htip, hcoords, hcore, hstrict⟩ :=
    goodRibbonPrefix_coordinates γ hw.1 _ hemb hi g hg hg0 hk hpref
  have hxq : |x| ≤ 1 / 4 := hx.trans (by linarith)
  have hx1 : |x| ≤ 1 := hxq.trans (by norm_num)
  have htipre : (xp T).re = fitCompletion s w m := by simp [htip]
  have htipim : (xp T).im = x := by simp [htip]
  have hfresh := ribbon_front_tip_survives_prior _ hP.continuousOn hi hH hescape γ xp T
    hxpc hxp0 hcoords hγeq (fun t ht => by rw [htipre]; exact hstrict t ht)
    (by rw [htipim]; exact hxq.trans_lt (by norm_num))
  have htipphysical : physicalFitChart s w m ((fitCompletion s w m : ℂ) + (x : ℂ) * Complex.I) = γ T := by
    push_cast at htip
    rw [← htip]
    exact (hγeq ⟨bot_le, le_rfl⟩).symm
  let α := fun u : ℝ≥0 => completeMarkedAccess s w m x u
  have hαc : Continuous α :=
    (completeMarkedAccess_continuous hs hs1 w hwy hwn hwr hm x).comp NNReal.continuous_coe
  have hαi : Function.Injective α := by
    intro t u he
    apply NNReal.coe_injective
    exact completeMarkedAccess_injective hs hs1 w hwy hwn hwr hm hx1 t.coe_nonneg u.coe_nonneg he
  have hα0 : α 0 = γ T := by
    change completeMarkedAccess s w m x (0 : ℝ) = γ T
    rw [completeMarkedAccess_zero hs hs1 w hwy hwn hm x, htipphysical]
  have hαD := completeMarkedAccess_survives hs hs1 w hwy hwn hwr hm hxq γ xp T hcoords hγeq
    (fun t ht => (hcore t ht).1)
  have hαescape : Tendsto α atTop (cocompact ℂ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop 0
    simp only [dist_zero_right]
    exact (completeMarkedAccess_norm_tendsto hs w hwn hwr m x).comp
      (NNReal.tendsto_coe_atTop.mpr tendsto_id)
  have hlocus (z : ℂ) (hz : z ∈ ball (0 : ℂ) ((s / 20) / 12)) :
      (∃ u : ℝ≥0, 0 < u ∧ α u = markedCornerChart w z) ↔ z.im = 0 :=
    completeMarkedAccess_corner_nnreal_iff hs hs1 w hwy hwn hwr hm hx1 hz
  have hclear (right : Bool) (t : ℝ) (ht : t ∈ Icc (1 / 64 : ℝ) 3) (u : ℝ≥0) (_hu : 0 < u) :
      (s / 20) / 1000 ≤ dist (markedWindowRoute right w (s / 20) t) (α u) := by
    have hh := completeMarkedAccess_route_clearance hs hs1 w hwy hwn hwr hm hx1
      (show 1 / 64 ≤ 4 / 3 * t by linarith [ht.1]) u.coe_nonneg
    cases right
    · exact hh.1
    · exact hh.2
  have hpast := physicalFit_prefix_low_right hs w hwy hwr hm γ xp T hcoords hγeq
  have hh := hangle U γ G F hw hU T hT hfresh w hwn (show 2 * (s / 20) < w.im by linarith)
    hpast α hαc hαi hα0 hαD hαescape hlocus hclear
  simpa only [hfirst, WithTop.untopD_coe] using hh

end SLEExactGauge.Serpentine

end

end OAI

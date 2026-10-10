import OAI.Probability.SLE.Gauge.ActualMissedCell
import OAI.Probability.SLE.SausagePointBound

namespace OAI

/-! The missed-cell estimate from finite centered laws. Constants and the
physical mesh are uniform over interior cutoffs and moving grid centers. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

local instance coverProbabilityDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance coverProbabilityDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance coverProbabilityPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance coverProbabilityPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem uniform_actual_dense_cover_probability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hγm : ∀ t, Measurable (fun ω => γ ω t))
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (htrace : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W) :
    ∃ T b c : ℝ, 0 < T ∧ 0 < b ∧ 0 < c ∧ ∃ v : ℕ → ℝ,
      (∀ n, 0 < v n) ∧ Tendsto v atTop (𝓝 0) ∧
      ∀ η : ℝ, 0 < η → ∃ D : ℝ, 0 < D ∧
        ∀ (R : ℝ) (K : Set ℂ), K ⊆ closedBall 0 R → (∀ z ∈ K, η ≤ z.im) →
        ∀ᶠ n : ℕ in atTop, ∀ ij ∈ retainedCoverGridIndex R (coverRadius T n) K,
          P {ω | denseMissedCell κ T b c (v n) n ij (γ ω)} ≤
            ENNReal.ofReal (D * coverRadius T n ^ codimension κ *
              Real.exp (-Real.sqrt (n : ℝ) / 4)) := by
  classical
  obtain ⟨h, b, C, hh, hh1, hb, hC, δ, hδ, hdense⟩ :=
    uniform_actual_conditional_dense_test P κ hκ hκ8 B hB hBm hc hB0 γ G F hγm hw
      htrace hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW
  let q := Serpentine.experimentRadiusLevel h
  have hq : 0 ≤ q := Serpentine.experimentRadiusLevel_nonneg hh (by linarith)
  let T := 2 + q
  have hT : 0 < T := by dsimp only [T]; linarith
  have hgap : 1 + q ≤ T := by dsimp only [T]; linarith
  let c := 1 / (2 * Real.sqrt C)
  have hcpos : 0 < c := by dsimp only [c]; positivity
  have hsmall : C * c ^ 2 ≤ 1 / 4 := by
    dsimp only [c]
    rw [div_pow, mul_pow, Real.sq_sqrt hC.le]
    field_simp [hC.ne']; norm_num
  let δ' (N : ℕ) := if N = 0 then 1 else δ N
  have hδ' (N : ℕ) : 0 < δ' N := by
    dsimp only [δ']
    split_ifs with hN
    · norm_num
    · exact hδ N (Nat.pos_of_ne_zero hN)
  obtain ⟨v, hv, hvlim, _, _, hvmesh⟩ := exists_cover_physical_mesh T c δ' hδ'
  refine ⟨T, b, c, hT, hb, hcpos, v, hv, hvlim, ?_⟩
  intro η hη
  let I := (2 : ℝ) ^ (-codimension κ) * (η / 2) ^ (-codimension κ)
  let D := uniformInverseAngleConstant κ 1 * (512 * Real.pi) ^ codimension κ * I
  have hIC : 0 < uniformInverseAngleConstant κ 1 :=
    uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num)
  have hI : 0 < I := by dsimp only [I]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro R K hK hheight
  have hgeom := eventually_retained_grid_cover_levels hT hη hK hheight
  have hheight' : ∀ᶠ n : ℕ in atTop, ∀ ij ∈ retainedCoverGridIndex R (coverRadius T n) K,
      η / 2 ≤ (coverGridCenter (coverRadius T n) ij).im := by
    filter_upwards [(coverRadius_tendsto_zero hT).eventually
      (gt_mem_nhds (show 0 < η / 4 by positivity))] with n hn
    intro ij hij
    have hz := (retainedCoverGrid_center_bounds hK hheight hij).2
    linarith
  filter_upwards [hgeom, hheight', coverMultiplicity_eventually_ge hcpos 1,
    denseVisit_probability_eventually_lower (by norm_num : (0 : ℝ) < 1 / 2) hC.le hcpos hsmall,
    eventually_ge_atTop (1 : ℕ)] with n hngeom hnheight hN hnprob hn1
  intro ij hij
  let z := coverGridCenter (coverRadius T n) ij
  obtain ⟨hz, hlevel, _, hvisit, hmeshsmall⟩ := hngeom ij hij
  have hNpos : 0 < coverMultiplicity c n := lt_of_lt_of_le Nat.zero_lt_one hN
  have hV := coverVisitLevel_nonneg_of_gap z T n hvisit
  have hfailed := actual_dense_window_failure_bound P κ hκ hκ8 B hB hBm hc hB0 γ G F hw
    z hz T q b (v n) C (coverVisitLevel z T n) hT.le hq hgap hV
    (coverMultiplicity c n) n hn1 hlevel hnprob ?_
  · have hmiss := actual_missed_cell_bound_of_centered_failure P κ hκ hκ8 B hB hBm hc hB0
      γ G F hw htrace T q b c (v n) hT.le hq hgap n ij hz hlevel hvisit hmeshsmall hfailed
    refine hmiss.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp : 0 ≤ codimension κ := by dsimp only [codimension, dimension]; linarith
    have hIz : initialGreen κ z ≤ I :=
      (initialGreen_le_height κ hκ hκ8 z hz).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (half_pos hη) (hnheight ij hij) (neg_nonpos.mpr hp))
          (Real.rpow_nonneg (by norm_num) _))
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (coverRadius_pos T n).le _)
    exact mul_le_mul_of_nonneg_left hIz
      (mul_nonneg hIC.le (Real.rpow_nonneg (by positivity) _))
  · intro j hj A hA
    have hr := radius_target_eq_coverRadius z hz T j (hlevel j hj)
    have hr' : (2 * z.im) * Real.exp (-(coverLogLevel z T j + 1)) =
        Real.exp (-1) * coverRadius T j := by
      rw [neg_add, Real.exp_add, ← mul_assoc, hr]
      ring
    have hcut : v n < δ (coverMultiplicity c n) * ((2 * z.im) *
        Real.exp (-(coverLogLevel z T j + 1))) := by
      have hhmesh := hvmesh n j hj
      rw [hr']
      dsimp only [δ'] at hhmesh
      rw [ite_eq_right (Nat.ne_of_gt hNpos)] at hhmesh
      simpa only [mul_comm] using hhmesh
    have hend : coverLogLevel z T j + 1 + q ≤ coverVisitLevel z T n := by
      have he := coverLogLevel_next_gap z T j (hlevel j hj)
      have hjlast : j + 1 ≤ 2 * n / 3 + 1 :=
        Nat.add_le_add_right (Finset.mem_Icc.mp hj).2 1
      have hm := coverLogLevel_monotone z hT.le hjlast
      linarith
    have hd := hdense z hz (coverLogLevel z T j) (coverLogLevel_nonneg _ _ _)
      (coverMultiplicity c n) hNpos (v n) (hv n) hcut (coverVisitLevel z T n) hend A hA
    simpa only [hr', actualDenseScaleTest, q] using hd

end SLEExactGauge

end

end OAI

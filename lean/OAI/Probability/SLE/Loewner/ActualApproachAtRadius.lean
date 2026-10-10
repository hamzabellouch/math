import OAI.Probability.SLE.Loewner.ActualApproach
import OAI.Probability.SLE.Loewner.ActualRadiusStopsRegular
import OAI.Probability.SLE.Gauge.ExtendedExperimentStop

namespace OAI

/-! The conditional approach estimate on the whole past of an actual
radius stop, including samples where that stop is never reached. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance radiusApproachDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance radiusApproachDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

theorem actual_radius_level_finite_state
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (z : ℂ) (u : ℝ) (hfinite : radiusLevelTime γ G z u ≠ ∞) :
    z ∈ survivingDomain γ (radiusLevelTime γ G z u).toNNReal ∧
      fullRadius G (radiusLevelTime γ G z u).toNNReal z = (2 * z.im) * Real.exp (-u) := by
  obtain ⟨T, hT, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u (lt_top_iff_ne_top.mpr hfinite)
  rw [radiusLevelTime_eq_of_live_level hU hw z u T hT hR, ENNReal.toNNReal_coe]
  exact ⟨hT, hR⟩

theorem actual_conditional_approach_at_radius_stop
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (htrace : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (v : ℝ≥0) (hv : 1 ≤ (v : ℝ))
    (A : Set Ω)
    (hA : MeasurableSet[(actual_radiusLevelTime_stopping hB
      (fun _t => hBm.comp (measurable_const.prodMk measurable_id)) hBm hc hB0
      κ hκ hκ8 γ G F hw z hz u hu).measurableSpace] A) :
    P (A ∩ {ω | radiusLevelTime (γ ω) (G ω) z (u + v) < ∞}) ≤
      ENNReal.ofReal (uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        ((2 * z.im) * Real.exp (-u)) ^ codimension κ * initialGreen κ z) *
        finiteCenteredLaw P κ B γ G z (u + v) A := by
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let σ : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  have hσ := actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz u hu
  let Q := finiteCenteredLaw P κ B γ G z (u + v)
  let K := ENNReal.ofReal (uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
    ((2 * z.im) * Real.exp (-u)) ^ codimension κ * initialGreen κ z)
  let T : Set Ω := {ω | radiusLevelTime (γ ω) (G ω) z (u + v) < ∞}
  let D (n : ℕ) := A ∩ {ω | σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}
  have hmono : Monotone (fun n => D n ∩ T) := by
    intro n k hnk ω hω
    refine ⟨⟨hω.1.1, ?_⟩, hω.2⟩
    change σ ω ≤ ((k : ℝ≥0) : WithTop ℝ≥0)
    exact hω.1.2.trans (WithTop.coe_le_coe.mpr (by exact_mod_cast hnk))
  have hcover : A ∩ T = ⋃ n, D n ∩ T := by
    ext ω
    constructor
    · rintro ⟨hωA, hωT⟩
      have hfinite : σ ω ≠ ⊤ := by
        have hlt := (radiusLevelTime_mono ((hc ω).const_mul _) (hw ω) z hu
          (show u ≤ u + v by linarith [v.coe_nonneg])).trans_lt hωT
        exact hlt.ne
      lift σ ω to ℝ≥0 using hfinite with t ht
      obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
      apply mem_iUnion.mpr
      refine ⟨n, ⟨hωA, ?_⟩, hωT⟩
      change σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)
      rw [← ht]
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast hn)
    · intro hω
      obtain ⟨n, hn⟩ := mem_iUnion.mp hω
      exact ⟨hn.1.1, hn.2⟩
  have hlocal (n : ℕ) : P (D n ∩ T) ≤ K * Q A := by
    let τ := cutoffStop σ (n : ℝ≥0)
    have hτ := cutoffStop_stopping _ σ hσ (n : ℝ≥0)
    have hD := cutoffStop_success_measurable _ σ hσ (n : ℝ≥0) A hA
    have hstate (ω : Ω) (hω : ω ∈ D n) :
        z ∈ survivingDomain (γ ω) (τ ω) ∧
          fullRadius (G ω) (τ ω) z = (2 * z.im) * Real.exp (-u) := by
      have hfin : radiusLevelTime (γ ω) (G ω) z u ≠ ∞ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top hω.2
      have he : τ ω = (radiusLevelTime (γ ω) (G ω) z u).toNNReal :=
        cutoffStop_eq_on_success σ _ ω hω.2
      rw [he]
      exact actual_radius_level_finite_state (hw ω) ((hc ω).const_mul _) z u hfin
    have hh := actual_conditional_radius_approach P κ hκ hκ8 B hB hBm hc hB0 γ G F hw htrace
      τ hτ z hz u hu v hv (D n) hD (fun ω hω => (hstate ω hω).1)
      (fun ω hω => (hstate ω hω).2) (D n) hD
    simp only [inter_self] at hh
    exact hh.trans (mul_le_mul' le_rfl (measure_mono inter_subset_left))
  change P (A ∩ T) ≤ K * Q A
  rw [hcover, hmono.measure_iUnion]
  exact iSup_le hlocal

end SLEExactGauge

end

end OAI

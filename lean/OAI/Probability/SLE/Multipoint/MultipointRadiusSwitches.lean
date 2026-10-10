import OAI.Probability.SLE.Loewner.ActualRadiusStopsRegular
import OAI.Probability.SLE.Gauge.ExtendedExperimentStop

namespace OAI

/-! The three actual radius switches of one multipoint factor: activation,
the midpoint of its radius clock, and completion. They reuse the literal
radius-level stopping times and are truncated only at the common finite
localization horizon. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge.Multipoint

def switchLevel (R b e : ℝ) (j : Fin 3) : ℝ :=
  if j = 0 then Real.log (R / b)
  else if j = 1 then (Real.log (R / b) + Real.log (R / e)) / 2
  else Real.log (R / e)

lemma switchLevel_nonneg {R b e : ℝ} (he : 0 < e) (heb : e ≤ b) (hbR : b ≤ R)
    (j : Fin 3) : 0 ≤ switchLevel R b e j := by
  have hb := he.trans_le heb
  have h₀ := Real.log_nonneg ((one_le_div hb).mpr hbR)
  have h₂ := Real.log_nonneg ((one_le_div he).mpr (heb.trans hbR))
  fin_cases j <;> norm_num [switchLevel] <;> linarith

lemma switchLevel_monotone {R b e : ℝ} (he : 0 < e) (heb : e ≤ b) (hbR : b ≤ R) :
    Monotone (switchLevel R b e) := by
  have hb := he.trans_le heb
  have hR := hb.trans_le hbR
  have hle : Real.log (R / b) ≤ Real.log (R / e) :=
    Real.log_le_log (div_pos hR hb) (div_le_div_of_nonneg_left hR.le he heb)
  intro i j hij
  dsimp only [switchLevel]
  split_ifs <;> first | omega | linarith

lemma switchLevel_midpoint_offset {R b e : ℝ} (hR : 0 < R) (hb : 0 < b) (he : 0 < e) :
    switchLevel R b e 1 - switchLevel R b e 0 = Real.log (b / e) / 2 := by
  norm_num [switchLevel,
    Real.log_div hR.ne' hb.ne', Real.log_div hR.ne' he.ne', Real.log_div hb.ne' he.ne']
  ring

lemma switchLevel_completion_offset {R b e : ℝ} (hR : 0 < R) (hb : 0 < b) (he : 0 < e) :
    switchLevel R b e 2 - switchLevel R b e 0 = Real.log (b / e) := by
  norm_num [switchLevel,
    Real.log_div hR.ne' hb.ne', Real.log_div hR.ne' he.ne', Real.log_div hb.ne' he.ne']

end SLEExactGauge.Multipoint

namespace SLEExactGauge

lemma cutoffStop_le_horizon {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0) (ω : Ω) :
    cutoffStop τ H ω ≤ H := by
  apply WithTop.coe_le_coe.mp
  rw [cutoffStop_coe]
  exact min_le_right _ _

lemma cutoffStop_mono {Ω : Type*} {σ τ : Ω → WithTop ℝ≥0}
    (hστ : ∀ ω, σ ω ≤ τ ω) (H : ℝ≥0) (ω : Ω) :
    cutoffStop σ H ω ≤ cutoffStop τ H ω := by
  apply WithTop.coe_le_coe.mp
  rw [cutoffStop_coe, cutoffStop_coe]
  exact min_le_min (hστ ω) le_rfl

/-- Concrete activation, midpoint, and completion stopping times for a
regular actual SLE, all localized at the same horizon. -/
theorem actual_radius_factor_switches
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane)
    (R b e : ℝ) (he : 0 < e) (heb : e ≤ b) (hbR : b ≤ R) (H : ℝ≥0) :
    let τ := fun j : Fin 3 => cutoffStop
      (fun ω => radiusLevelTime (γ ω) (G ω) z (Multipoint.switchLevel R b e j)) H
    (∀ j, IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ j ω : WithTop ℝ≥0))) ∧
    (∀ ω, Monotone (fun j => τ j ω)) ∧ (∀ j ω, τ j ω ≤ H) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact cutoffStop_stopping _ _
      (actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz
        (Multipoint.switchLevel R b e j) (Multipoint.switchLevel_nonneg he heb hbR j)) H
  · intro ω i j hij
    apply cutoffStop_mono _ H ω
    intro ω'
    exact radiusLevelTime_mono ((hc ω').const_mul _) (hw ω') z
      (Multipoint.switchLevel_nonneg he heb hbR i)
      (Multipoint.switchLevel_monotone he heb hbR hij)
  · exact fun j ω => cutoffStop_le_horizon _ H ω

end SLEExactGauge

end

end OAI

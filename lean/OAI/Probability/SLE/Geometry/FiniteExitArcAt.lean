import OAI.Probability.SLE.Mass.WaypointHarmonicMeasure

namespace OAI

/-! Identify exit arcs from any strictly positive local departure time.
This permits a short initial departure inside a marked corner chart. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.RibbonCoordinates
open Target CrosscutSides

theorem finite_exit_event_measure_le_arc_at
    (μ : Measure (Driver × Driver)) (D : Set ℂ) (g : ℂ → ℂ) (w : ℂ)
    (h : ℂ ≃ₜ ℂ) (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (hg : ContinuousOn g D) (E : Set (Driver × Driver)) {dir a : ℝ}
    (hdir : dir = -1 ∨ dir = 1) (ha : 0 ≤ a)
    (hexit : ∀ᵐ b ∂μ, ∀ τ : ℝ, UnitWindowFirstExit D (physicalUnitBrownianPath w b) τ →
      ∃ x : ℝ, x ≠ 0 ∧ Tendsto (fun t => g (physicalUnitBrownianPath w b t))
        (𝓝[<] τ) (𝓝 (x : ℂ)))
    (hgeom : ∀ b ∈ E, ∃ τ : ℝ,
      UnitWindowFirstExit D (physicalUnitBrownianPath w b) τ ∧ a < τ ∧
      ∀ t ∈ Ico a τ, (h (g (physicalUnitBrownianPath w b t))).re ≠ 0)
    (hstart : ∀ b ∈ E, 0 < dir * (h (g (physicalUnitBrownianPath w b a))).re) :
    μ E ≤ μ (unitWindowExitArc D g w dir) := by
  apply measure_mono_ae
  filter_upwards [hexit] with b hb
  intro he
  obtain ⟨τ, hτ, haτ, hn⟩ := hgeom b he
  obtain ⟨x, hx, hlim⟩ := hb τ hτ
  refine ⟨τ, hτ, x, ?_, hlim⟩
  let ζ := physicalUnitBrownianPath w b
  have hj : ContinuousOn (fun z => (h (g z)).re) D :=
    Complex.continuous_re.comp_continuousOn (h.continuous.comp_continuousOn hg)
  have hin : MapsTo ζ (Ico a τ) D := hτ.2.2.mono_left (Ico_subset_Ico_left ha)
  have hs := hstart b he
  rcases hdir with rfl | rfl
  · have hp := exit_prefix_negative (fun z => (h (g z)).re) hj ζ
      (physicalUnitBrownianPath_continuous w b).continuousOn hin hn haτ (by nlinarith)
    have hxneg := real_exit_negative_of_straightened_prefix h hreal
      (fun t => g (ζ t)) haτ hx hp hlim
    nlinarith
  · have hp := exit_prefix_positive (fun z => (h (g z)).re) hj ζ
      (physicalUnitBrownianPath_continuous w b).continuousOn hin hn haτ (by simpa using hs)
    have hxpos := real_exit_positive_of_straightened_prefix h hreal
      (fun t => g (ζ t)) haτ hx hp hlim
    simpa using hxpos

end SLEExactGauge.RibbonCoordinates

end

end OAI

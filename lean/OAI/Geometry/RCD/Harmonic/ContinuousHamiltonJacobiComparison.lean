import OAI.Geometry.RCD.Harmonic.TimeAveragePairing

namespace OAI

/-! # Removing the time average in an endpoint action inequality -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem continuous_comparison_of_time_averages
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (H : ℝ → X → ℝ) (hH : Measurable (Function.uncurry H))
    {Ω : Set X} (hΩ : IsCompact Ω) {δ a b E : ℝ} {L : ℝ≥0}
    (hL : LipschitzOnWith L (Function.uncurry H) (Ioo δ 1 ×ˢ Ω))
    (e₀ e₁ : Y → X) (he₀ : Measurable e₀) (he₁ : Measurable e₁)
    (hs₀ : ∀ᵐ y ∂ν, e₀ y ∈ Ω) (hs₁ : ∀ᵐ y ∂ν, e₁ y ∈ Ω)
    (ha : δ < a) (hab : a < b) (hb : b < 1)
    (hav : ∀ h : ℝ, 0 < h → δ < a-h → b+h < 1 →
      (∫ y, timeIntervalAverage (fun q => H q (e₀ y)) h a ∂ν) -
        (∫ y, timeIntervalAverage (fun q => H q (e₁ y)) h b ∂ν) ≤ E) :
    (∫ y, H a (e₀ y) ∂ν)-(∫ y, H b (e₁ y) ∂ν) ≤ E := by
  let M := ν.real univ*(L:ℝ)
  have hM : 0 ≤ M := mul_nonneg measureReal_nonneg L.coe_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  have hsmall : 0 < min ((a-δ)/2) (min ((1-b)/2) (ε/(2*(M+1)))) := by positivity
  obtain ⟨h,hh,hlim⟩ := exists_between hsmall
  have hha : h < (a-δ)/2 := hlim.trans_le (min_le_left _ _)
  have hrest := hlim.trans_le (min_le_right _ _)
  have hhb : h < (1-b)/2 := hrest.trans_le (min_le_left _ _)
  have hhM : h < ε/(2*(M+1)) := hrest.trans_le (min_le_right _ _)
  have hha' : δ < a-h := by linarith
  have hhb' : b+h < 1 := by linarith
  have herror : 2*M*h < ε := by
    have hm := (lt_div_iff₀ (by positivity : 0 < 2*(M+1))).mp hhM
    nlinarith
  have he₀ := time_average_pairing_error ν H hH hΩ hL e₀ he₀ hs₀ hh hha'
    (show a+h < 1 by linarith)
  have he₁ := time_average_pairing_error ν H hH hΩ hL e₁ he₁ hs₁ hh
    (show δ < b-h by linarith) hhb'
  have hcmp := hav h hh hha' hhb'
  have h₀ := (abs_le.mp he₀).1
  have h₁ := (abs_le.mp he₁).2
  dsimp only [M] at herror
  nlinarith

end RegularPointCoordinates

end

end OAI

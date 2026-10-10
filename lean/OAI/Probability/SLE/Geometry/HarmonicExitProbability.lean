import OAI.Probability.SLE.Geometry.HarmonicExitLimit

namespace OAI

/-! Positive bounded harmonic terminal tests control finite-exit events
without requiring measurability of the event's existential description. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma terminal_threshold_measure_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Y : Ω → ℝ) (hY : Integrable Y P)
    (hpos : ∀ᵐ b ∂P, 0 ≤ Y b) (E : Set Ω) (a : ℝ) (ha : 0 ≤ a)
    (hE : ∀ᵐ b ∂P, b∈E → a ≤ Y b) :
    ENNReal.ofReal a*P E ≤ ENNReal.ofReal (∫ b, Y b ∂P) := by
  have hh := mul_meas_ge_le_integral_of_nonneg hpos hY a
  have hmarkov : ENNReal.ofReal a*P {b | a ≤ Y b} ≤ ENNReal.ofReal (∫ b, Y b ∂P) := by
    have h := ENNReal.ofReal_le_ofReal hh
    simpa only [ENNReal.ofReal_mul ha,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  exact (mul_le_mul' le_rfl (measure_mono_ae hE)).trans hmarkov

namespace SmoothDomainExhaustion
variable {U : Set (ℝ×ℝ)} (e : SmoothDomainExhaustion U 0)

include e in
theorem nonnegative_harmonic_exit_bound
    (W : WienerLaw) (hW : IsWiener W) (T : ℝ≥0) (hU : IsOpen U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (C : ℝ≥0) (huC : ∀ z∈U, |u z|≤C) (hpos : ∀ z∈U, 0 ≤ u z)
    (E : Set (Driver×Driver)) (a : ℝ) (ha : 0 ≤ a)
    (hE : ∀ b∈E, ∃ τ : ℝ≥0, 0 < τ ∧ τ ≤ T ∧
      (∀ t<τ, planarWiener t b∈U) ∧ planarWiener τ b∉U ∧
      Tendsto (fun t => u (planarWiener t b)) (𝓝[<] τ) (𝓝 a)) :
    ENNReal.ofReal a*(W.prod W) E ≤ ENNReal.ofReal (u 0) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Y,hYm,hYb,hmean,hYconv,hYexit⟩ := e.harmonic_exit_limit W hW T hU u hu hhar C huC
  have hYi : Integrable Y (W.prod W) := Integrable.of_bound hYm.aestronglyMeasurable C
    (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hYb b)
  have hYpos : ∀ᵐ b ∂W.prod W, 0 ≤ Y b := by
    filter_upwards [hYconv] with b hb
    exact ge_of_tendsto hb (Eventually.of_forall fun n =>
      hpos _ (e.stop_mem_domain T n b _ le_rfl))
  have hevent : ∀ᵐ b ∂W.prod W, b∈E → a ≤ Y b := by
    filter_upwards [hYexit] with b hb
    intro hbe
    obtain ⟨τ,hτ,hτT,hp,hx,hl⟩ := hE b hbe
    let : NeBot (𝓝[<] τ) := nhdsLT_neBot_of_exists_lt ⟨0,hτ⟩
    exact (tendsto_nhds_unique (hb τ hτT hp hx) hl).symm.le
  simpa only [hmean] using terminal_threshold_measure_le (W.prod W) Y hYi hYpos E a ha hevent

end SmoothDomainExhaustion

end SLEExactGauge

end

end OAI

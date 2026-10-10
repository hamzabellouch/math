import OAI.Probability.SLE.Loewner.LoewnerCompactDriverNeighborhood
import OAI.Probability.SLE.Stochastic.BrownianFiniteTube
import OAI.Probability.SLE.Geometry.ActualFirstHeightSupport

namespace OAI

/-! Positive probability of preserving a compact surviving set of a
prescribed continuous Loewner driver. This controls compact interior
obstacles in the geometric-support construction. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem regular_scaled_driver_tube_positive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (V : C(ℝ≥0,ℝ)) (hV0 : V 0=0)
    (T : ℝ≥0) (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ) :
    0 < (P.comap (Subtype.val : a.samples → Ω))
      {ω | ∀ t ∈ Icc 0 T, |Real.sqrt κ*a.B t ω-V t| < δ} := by
  have hroot : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  let f : C(ℝ≥0,ℝ) := ⟨fun t => V t / Real.sqrt κ,
    V.continuous.div_const _⟩
  have hf0 : f 0=0 := by simp [f,hV0]
  have hp := brownian_finite_uniform_tube_positive a.B a.brownian a.measurable_B
    a.continuous_B a.zero_B T hT f hf0 (div_pos hδ hroot)
  apply hp.trans_le (measure_mono ?_)
  intro ω hω t ht
  have hh := hω t ht
  change |a.B t ω-V t / Real.sqrt κ| < δ/Real.sqrt κ at hh
  have he : Real.sqrt κ*a.B t ω-V t =
      Real.sqrt κ*(a.B t ω-V t/Real.sqrt κ) := by field_simp
  rw [he,abs_mul,abs_of_pos hroot]
  simpa only [mul_comm] using (lt_div_iff₀ hroot).mp hh

theorem regular_compact_survival_positive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (V : C(ℝ≥0,ℝ)) (hV0 : V 0=0)
    {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0) (hT : 0 < T)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ survivingDomain β T) :
    0 < (P.comap (Subtype.val : a.samples → Ω))
      {ω | K ⊆ survivingDomain (γ ω) T} := by
  obtain ⟨δ,hδ,hkeep⟩ := driver_neighborhood_preserves_compact hv T hK hKD
  have hp := regular_scaled_driver_tube_positive a hκ V hV0 T hT hδ
  apply hp.trans_le (measure_mono ?_)
  intro ω hω
  apply hkeep (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (a.F ω) (a.witness ω)
  exact fun t ht => (hω t ht).le

theorem ordinary_compact_survival_positive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (γ : Ω → ℝ≥0 → ℂ)
    (hSLE : IsOrdinaryChordalSLE κ γ P)
    (V : C(ℝ≥0,ℝ)) (hV0 : V 0=0)
    {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0) (hT : 0 < T)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ survivingDomain β T) :
    0 < P {ω | K ⊆ survivingDomain (γ ω) T} := by
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  have hp := regular_compact_survival_positive a hκ V hV0 hv T hT hK hKD
  apply hp.trans_le
  have hh := Measure.le_map_apply (μ := P.comap (Subtype.val : a.samples → Ω))
    a.measurePreserving_val.measurable.aemeasurable
    {ω | K ⊆ survivingDomain (γ ω) T}
  rw [a.measurePreserving_val.map_eq] at hh
  convert! hh using 1

end SLEExactGauge

end

end OAI

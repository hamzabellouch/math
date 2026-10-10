import OAI.Probability.SLE.Geometry.FirstHeightSupport
import OAI.Probability.SLE.Loewner.ScaleTraceLaw

namespace OAI

/-! The scale-independent narrow first-height probability follows from the
proved equality of actual scaled trace laws and an exact tube-event scaling
identity. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.FirstHeightSupport

local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

/-- Capacity scaling sends a narrow-rise event to exactly the correspondingly
scaled narrow-rise event, including its finite time witness. -/
theorem scalePath_narrowRiseEvent_iff
    (p : C(ℝ≥0, ℂ)) (c : ℝ≥0) (hc : 0 < c) (B : ℝ) :
    ScaleTraceLaw.scalePath c p ∈ narrowRiseEvent ((c : ℝ) * B) ↔ p ∈ narrowRiseEvent B := by
  have hcR : 0 < (c : ℝ) := hc
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hre (t : ℝ≥0) : |(ScaleTraceLaw.scalePath c p t).re| =
      (c : ℝ) * |(p (sourceScaleTime c t)).re| := by
    change |((c : ℂ) * p (sourceScaleTime c t)).re| = _
    simp [Complex.mul_re, abs_mul, abs_of_nonneg c.coe_nonneg]
  have him (t : ℝ≥0) : (ScaleTraceLaw.scalePath c p t).im =
      (c : ℝ) * (p (sourceScaleTime c t)).im := by
    change ((c : ℂ) * p (sourceScaleTime c t)).im = _
    simp [Complex.mul_im]
  constructor
  · rintro ⟨S, hS, hN, hV⟩
    refine ⟨sourceScaleTime c S, div_pos hS hc2, ?_, ?_⟩
    · intro t ht
      have hv : t * c ^ 2 ∈ Icc (0 : ℝ≥0) S :=
        ⟨bot_le, (le_div_iff₀ hc2).mp ht.2⟩
      have hh : |(ScaleTraceLaw.scalePath c p (t * c ^ 2)).re| < (c : ℝ) * B / 16 := hN hv
      rw [hre] at hh
      simp only [sourceScaleTime, mul_div_cancel_right₀ _ (ne_of_gt hc2)] at hh
      apply (mul_lt_mul_iff_right₀ hcR).mp
      nlinarith
    · have hh : (c : ℝ) * B / 4 < (ScaleTraceLaw.scalePath c p S).im := hV
      rw [him] at hh
      apply (mul_lt_mul_iff_right₀ hcR).mp
      nlinarith
  · rintro ⟨T, hT, hN, hV⟩
    refine ⟨T * c ^ 2, mul_pos hT hc2, ?_, ?_⟩
    · intro t ht
      have hu : sourceScaleTime c t ∈ Icc (0 : ℝ≥0) T :=
        ⟨bot_le, (div_le_iff₀ hc2).mpr ht.2⟩
      change |(ScaleTraceLaw.scalePath c p t).re| < (c : ℝ) * B / 16
      rw [hre]
      have hh : |(p (sourceScaleTime c t)).re| < B / 16 := hN hu
      nlinarith
    · change (c : ℝ) * B / 4 < (ScaleTraceLaw.scalePath c p (T * c ^ 2)).im
      rw [him]
      simp only [sourceScaleTime, mul_div_cancel_right₀ _ (ne_of_gt hc2)]
      have hh : B / 4 < (p T).im := hV
      nlinarith

/-- Narrow-rise probabilities for actual chordal SLE are invariant under
simultaneous spatial and capacity-time scaling. -/
theorem narrowRise_probability_scaling
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω) (γ ω) (G ω) (F ω))
    (c : ℝ≥0) (hcpos : 0 < c) (B : ℝ) :
    P {ω | sourceTracePath γ (fun ω => (hw ω).1) ω ∈ narrowRiseEvent ((c : ℝ) * B)} =
      P {ω | sourceTracePath γ (fun ω => (hw ω).1) ω ∈ narrowRiseEvent B} := by
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  obtain ⟨Φ, hΦm, hΦ, _⟩ := sourceStoppedTraceLaw κ hκ hκ8 B₀ hB₀ hm hc γ G F hw
  have hgm : Measurable gp := by
    have he : gp = Φ ∘ sourceDriverPath B₀ hc := funext fun ω => (hΦ ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable _ hm)
  have he := congrArg (fun μ : Measure C(ℝ≥0, ℂ) => μ (narrowRiseEvent ((c : ℝ) * B)))
    (ScaleTraceLaw.scaled_trace_path_law κ hκ hκ8 B₀ hB₀ hm hc γ G F hw c hcpos)
  change (P.map (ScaleTraceLaw.scalePath c ∘ gp)) (narrowRiseEvent ((c : ℝ) * B)) =
    (P.map gp) (narrowRiseEvent ((c : ℝ) * B)) at he
  rw [Measure.map_apply ((ScaleTraceLaw.measurable_scalePath c).comp hgm)
      (measurableSet_narrowRiseEvent _),
    Measure.map_apply hgm (measurableSet_narrowRiseEvent _)] at he
  have hset : {ω | ScaleTraceLaw.scalePath c (gp ω) ∈ narrowRiseEvent ((c : ℝ) * B)} =
      {ω | gp ω ∈ narrowRiseEvent B} := by
    ext ω
    exact scalePath_narrowRiseEvent_iff (gp ω) c hcpos B
  change P {ω | ScaleTraceLaw.scalePath c (gp ω) ∈ narrowRiseEvent ((c : ℝ) * B)} =
    P {ω | gp ω ∈ narrowRiseEvent ((c : ℝ) * B)} at he
  rw [hset] at he
  exact he.symm

/-- One fixed positive probability works for the narrow first-height event
at every spatial scale. Its equality of laws has been proved above. -/
theorem uniform_narrowFirstHeight_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedGeometricTubeSupport P γ) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ B : ℝ, 0 < B → q ≤ P {ω | NarrowFirstHeight B (γ ω)} := by
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  let q := P {ω | gp ω ∈ narrowRiseEvent 1}
  have hq : 0 < q := narrowRiseEvent_positive P γ hpublished zero_lt_one
  refine ⟨q, hq, ?_⟩
  intro B hB
  let c : ℝ≥0 := ⟨B, hB.le⟩
  have he := narrowRise_probability_scaling κ hκ hκ8 B₀ hB₀ hm hc γ G F hw c hB 1
  have he' : P {ω | gp ω ∈ narrowRiseEvent B} = q := by
    have hcval : (c : ℝ) = B := rfl
    change P {ω | gp ω ∈ narrowRiseEvent ((c : ℝ) * 1)} = q at he
    simpa only [hcval, mul_one] using he
  rw [← he']
  apply measure_mono
  intro ω hω
  exact narrowRiseEvent_gives_first_height hB (gp ω) (hw ω).2.1 (hw ω).2.2.1 hω

end SLEExactGauge.FirstHeightSupport

end

end OAI

import OAI.Probability.SLE.Geometry.BoundedTerminalMean

namespace OAI

/-! The upper cover is charged to the canonical terminal measure on the
physical plane. Its mean is the initial Green measure, also on sets meeting
the real boundary. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

def RationalCanonicalMass.physicalTerminal (C : RationalCanonicalMass P κ B hBm γ G)
    (ω : Ω) : Measure ℂ := (C.terminal ω).map Subtype.val

lemma RationalCanonicalMass.physicalTerminal_measurable
    (C : RationalCanonicalMass P κ B hBm γ G) : Measurable C.physicalTerminal :=
  (Measure.measurable_map Subtype.val measurable_subtype_coe).comp C.terminal_measurable

lemma RationalCanonicalMass.physicalTerminal_apply
    (C : RationalCanonicalMass P κ B hBm γ G) (ω : Ω) {A : Set ℂ} (hA : MeasurableSet A) :
    C.physicalTerminal ω A = C.terminal ω (Subtype.val ⁻¹' A) :=
  Measure.map_apply measurable_subtype_coe hA

lemma RationalCanonicalMass.physicalTerminal_mean
    (C : RationalCanonicalMass P κ B hBm γ G) :
    P.bind C.physicalTerminal = (initialGreenMeasure κ).map Subtype.val := by
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA C.physicalTerminal_measurable.aemeasurable,
    Measure.map_apply measurable_subtype_coe hA,← C.mean,
    Measure.bind_apply (hA.preimage measurable_subtype_coe) C.terminal_measurable.aemeasurable]
  apply lintegral_congr
  intro ω
  exact C.physicalTerminal_apply ω hA

lemma RationalCanonicalMass.physicalTerminal_bounded_mean_lt_top
    (C : RationalCanonicalMass P κ B hBm γ G) (hκ : 0<κ) (hκ8 : κ<8) (R : ℝ) :
    (∫⁻ ω,C.physicalTerminal ω (closedBall 0 R) ∂P) < ∞ := by
  simp_rw [C.physicalTerminal_apply _ isClosed_closedBall.measurableSet]
  exact C.terminal_bounded_mean_lt_top hκ hκ8 R

end SLEExactGauge.Multipoint

end

end OAI

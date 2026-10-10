import OAI.Probability.SLE.Loewner.StoppedInverseTestUniqueness
import OAI.Probability.SLE.Loewner.StoppedInverseExhaustion

namespace OAI

/-! The finite-time restart identity extends to the locally exhausted
terminal mass using the same raw fresh functional. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance stoppedTerminalUniqueLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

lemma halfPlane_nested_remainder (a b c : Measure upperHalfPlane)
    [a.Regular] [b.Regular] (hab : a ≤ b) (hbc : b ≤ c) :
    (c-a)-(b-a)=c-b := by
  let := halfPlane_sub_finite_on_compacts b a
  apply (Measure.add_left_inj (b-a) _ _).mp
  have hle : b-a ≤ c-a := sub_le_sub_right_of_le (hab.trans hbc) hbc
  rw [sigmaFinite_sub_add_cancel_of_le hle]
  apply (Measure.add_left_inj a _ _).mp
  calc
    (c-a)+a = c := sigmaFinite_sub_add_cancel_of_le (hab.trans hbc)
    _ = (c-b)+b := (sigmaFinite_sub_add_cancel_of_le hbc).symm
    _ = ((c-b)+(b-a))+a := by rw [add_assoc,sigmaFinite_sub_add_cancel_of_le hab]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
  (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (R : RawCanonicalMass)
  (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
    R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
  (τ : Ω → ℝ≥0)
  (hτ : IsStoppingTime (Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
    (fun ω => (τ ω:WithTop ℝ≥0)))
  (hFresh : ∀ᵐ ω ∂P, ∃ (β : ℝ≥0 → ℂ) (G' F' : ℝ≥0 → ℂ → ℂ),
    IsCapacityTwoWitness (fun t => Real.sqrt κ*B (τ ω+t) ω-Real.sqrt κ*B (τ ω) ω) β G' F')


include C hB hc hκ F hw R he τ hτ hFresh in
theorem CanonicalMass.stoppedFreshTerminalMass_eq_remainder
    (hpaths : ∀ᵐ ω ∂P, PositiveMassPaths
      (fun t => stoppedFreshMass B κ γ G F hw τ hc R t ω)
      (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω))
    (hfin : ∀ᵐ ω ∂P,
      IsFiniteMeasureOnCompacts (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω))
    (hex : ∀ᵐ ω ∂P, ∀ K : Set upperHalfPlane, IsCompact K → Tendsto
      (fun t : ℝ≥0 => (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω-
        stoppedFreshMass B κ γ G F hw τ hc R t ω) K) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, C.rational.terminal ω-C.process (τ ω) ω =
      stoppedFreshTerminalMass B κ γ G F hw τ hc R ω := by
  filter_upwards [C.paths,C.exhaustion,hpaths,hfin,hex,
    C.stoppedFreshMass_indistinguishable hB hc hκ F hw R he τ hτ hFresh hpaths]
    with ω hp hx hq hf heq hid
  let := (C.rational.terminal_radon ω).1
  let := (C.radon (τ ω) ω).1
  let := halfPlane_sub_finite_on_compacts (C.rational.terminal ω) (C.process (τ ω) ω)
  let := hf
  apply radon_terminal_eq_of_common_exhaustion
    (C.rational.terminal ω-C.process (τ ω) ω)
    (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω)
    (fun t => stoppedFreshMass B κ γ G F hw τ hc R t ω)
  · intro t
    rw [← hid t]
    exact sub_le_sub_right_of_le (hp.dominated (τ ω)) (hp.dominated (τ ω+t))
  · exact hq.dominated
  · intro K hK
    have htime : Tendsto (fun t : ℝ≥0 => τ ω+t) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop b] with t ht
      exact ht.trans (le_add_of_nonneg_left (show 0 ≤ τ ω from zero_le))
    have hlimit := (hx K hK).comp htime
    have hrem (t : ℝ≥0) :
        (C.rational.terminal ω-C.process (τ ω) ω)-
          stoppedFreshMass B κ γ G F hw τ hc R t ω =
        C.rational.terminal ω-C.process (τ ω+t) ω := by
      rw [← hid t]
      let := (C.radon (τ ω+t) ω).1
      exact halfPlane_nested_remainder _ _ _
        (hp.monotone (le_add_of_nonneg_right (show 0 ≤ t from zero_le))) (hp.dominated _)
    simpa only [hrem,Function.comp_def] using hlimit
  · exact heq

end SLEExactGauge.Multipoint

end

end OAI

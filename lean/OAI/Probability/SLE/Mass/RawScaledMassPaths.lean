import OAI.Probability.SLE.Loewner.RawScaledGreenKernel
import OAI.Probability.SLE.Loewner.RawTerminalExhaustion
import OAI.Probability.SLE.Loewner.StoppedInversePaths

namespace OAI

/-! One raw canonical functional has a measurable full-law certificate
for continuous positive mass paths. Brownian scaling preserves it. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge.Multipoint

local instance rawScaledMassMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawScaledMassBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance rawScaledMassLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

omit [IsProbabilityMeasure P] in
lemma CanonicalMass.exists_raw_positive_paths (C : CanonicalMass P κ B hBm γ G)
    (hc : ∀ ω, Continuous (fun t => B t ω)) :
    ∃ R : RawCanonicalMass,
      (∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
        R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω) ∧
      ∃ E : Set C(ℝ≥0,ℝ), MeasurableSet E ∧
        (∀ᵐ p ∂P.map (sourceDriverPath B hc), p ∈ E) ∧
        ∀ p ∈ E, PositiveMassPaths (fun t => R.process t p) (R.terminal p) := by
  obtain ⟨N,E,hNp,hNr,hNn,hEm,hEf,hEp,he⟩ := C.exists_raw_nonanticipating_with_good_set hc
  let R : RawCanonicalMass := ⟨N,rawTerminalMass N,hNp,hNr,
    rawTerminalMass_measurable N hNp hNr,rawTerminalMass_radon N,hNn⟩
  obtain ⟨hTm,hTf,hTp⟩ := C.raw_terminal_good_set hc N hNp hNr he
  refine ⟨R,?_,E ∩ {p | RawTerminalGood (localTestFamily upperHalfPlane)
    (fun t => N t p) (rawTerminalMass N p)},hEm.inter hTm,?_,?_⟩
  · filter_upwards [he,C.rawTerminal_realizes hc N he] with ω hω ht
    exact ⟨hω,ht⟩
  · exact hEf.and hTf
  · intro p hp
    obtain ⟨hz,hm,hcont⟩ := hEp p hp.1
    exact ⟨hz,hm,(hTp p hp.2 hm).1,(fun t => hNr t p),fun f _ => hcont f⟩

def scaledRawMass (R : RawCanonicalMass) (c : ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (t : ℝ≥0) (ω : Ω) : Measure upperHalfPlane :=
  R.process (c^2*t) (sourceDriverPath (scaledBrownianDriver c B)
    (scaledBrownianDriver_continuous c B hc) ω)

def scaledRawTerminal (R : RawCanonicalMass) (c : ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (ω : Ω) : Measure upperHalfPlane :=
  R.terminal (sourceDriverPath (scaledBrownianDriver c B)
    (scaledBrownianDriver_continuous c B hc) ω)

lemma scaledRawMass_adapted (R : RawCanonicalMass) (c : ℝ≥0) (hcp : 0 < c)
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) :
    Adapted (Filtration.natural B (fun s => (hm s).stronglyMeasurable)) (scaledRawMass R c B hc) := by
  let ℱc := Filtration.natural (scaledBrownianDriver c B)
    (fun s => (scaledBrownianDriver_measurable c B hm s).stronglyMeasurable)
  let Y := sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hc)
  have hY : Adapted ℱc (fun t ω => Y ω t) := fun t =>
    (Filtration.stronglyAdapted_natural
      (fun s => (scaledBrownianDriver_measurable c B hm s).stronglyMeasurable) t).measurable
  have hp := (raw_process_comp_progressive ℱc Y hY R.process R.progressive).adapted
  intro t
  have h := hp (c^2*t)
  change Measurable[ℱc (c^2*t)] (scaledRawMass R c B hc t) at h
  rwa [show ℱc (c^2*t)=(Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t from
    scaledBrownianDriver_filtration c hcp B hm t] at h

omit [IsProbabilityMeasure P] in
lemma scaledRawMass_positive_paths
    (R : RawCanonicalMass) (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p ∈ E)
    (hEp : ∀ p ∈ E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (c : ℝ≥0) (hcp : 0 < c) :
    ∀ᵐ ω ∂P, PositiveMassPaths (fun t => scaledRawMass R c B hc t ω)
      (scaledRawTerminal R c B hc ω) := by
  have hY := source_path_measurable
    (sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hc))
    (scaledBrownianDriver_measurable c B hm)
  have hf : ∀ᵐ p ∂P.map (sourceDriverPath (scaledBrownianDriver c B)
      (scaledBrownianDriver_continuous c B hc)), p ∈ E := by
    rwa [scaledBrownianDriver_path_law c hcp B hB hm hc]
  filter_upwards [(ae_map_iff hY.aemeasurable hE).mp hf] with ω hω
  have hp := hEp _ hω
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [scaledRawMass,mul_zero] using hp.zero
  · intro s t hst
    exact hp.monotone (mul_le_mul_of_nonneg_left hst zero_le)
  · intro t
    exact hp.dominated (c^2*t)
  · intro t
    exact hp.radon (c^2*t)
  · intro f hfp
    exact (hp.continuous_tests f hfp).comp (continuous_const.mul continuous_id)

end SLEExactGauge.Multipoint

end

end OAI

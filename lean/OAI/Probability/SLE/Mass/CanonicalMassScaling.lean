import OAI.Probability.SLE.Mass.RawScaledMassMeans
import OAI.Probability.SLE.Mass.CanonicalMassPositiveReduction

namespace OAI

/-! Canonical mass is identified with its dimension-weighted dilation
by the proved Green kernel and continuous increasing-path uniqueness. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge.Multipoint

local instance canonicalScalingDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance canonicalScalingDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance canonicalScalingLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma CanonicalMass.scaled_raw_process_eq
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p ∈ E)
    (hEp : ∀ p ∈ E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (c : ℝ≥0) (hcp : 0 < c) :
    ∀ᵐ ω ∂P, ∀ t, dilationMass κ c hcp (C.process t ω)=scaledRawMass R c B hc t ω := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hd : Measurable (dilationMass κ c hcp) := conformalMass_measurable _ _
  have hA : Adapted (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun t ω => dilationMass κ c hcp (C.process t ω)) :=
    fun t => hd.comp (C.progressive.adapted t)
  have hZ : Measurable (scaledRawTerminal R c B hc) := R.terminal_measurable.comp
    (source_path_measurable _ (scaledBrownianDriver_measurable c B hm))
  have hAb (t : ℝ≥0) : P.bind (fun ω => dilationMass κ c hcp (C.process t ω)) ≤
      initialGreenMeasure κ := by
    rw [dilationMass_bind P κ c hcp _ (C.progressive.adapted.measurable (i:=t))]
    apply (dilationMass_mono κ c hcp ?_).trans_eq (dilationMass_initialGreen κ c hcp)
    simpa only [Measure.restrict_univ] using C.uniqueness_process_mean_le t univ
  have hAT : P.bind (fun ω => dilationMass κ c hcp (C.rational.terminal ω)) ≤
      initialGreenMeasure κ := by
    rw [dilationMass_bind P κ c hcp _ C.rational.terminal_measurable,C.rational.mean,
      dilationMass_initialGreen]
  have hpaths : ∀ᵐ ω ∂P, PositiveMassPaths
      (fun t => dilationMass κ c hcp (C.process t ω))
      (dilationMass κ c hcp (C.rational.terminal ω)) := by
    filter_upwards [C.paths] with ω hp
    refine ⟨?_,?_,?_,?_,?_⟩
    · simp only [hp.zero,dilationMass,conformalMass_zero]
    · intro s t hst
      exact dilationMass_mono κ c hcp (hp.monotone hst)
    · intro t
      exact dilationMass_mono κ c hcp (hp.dominated t)
    · intro t
      let := (C.radon t ω).2
      exact conformalMass_radon _ _ _
    · intro f _hf
      exact conformalMass_test_continuous _ _ _ hp.continuous_tests f
  exact positive_mass_process_eq_of_cross_kernel _ _ _ _ hA
    (scaledRawMass_adapted R c hcp B hm hc) (hd.comp C.rational.terminal_measurable) hZ
    hAb (C.scaledRawMass_mean_le hB hc R he c hcp)
    hAT (le_of_eq (C.scaledRawTerminal_mean hB hc R he c hcp)) hpaths
    (scaledRawMass_positive_paths R E hE B hB hm hc hEf hEp c hcp)
    (C.scaledRawMass_cross_kernel hB hc R he c hcp F hw)

lemma CanonicalMass.nonzero_probability_scaled
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (c : ℝ≥0) (hcp : 0 < c) (t : ℝ≥0) :
    P {ω | C.process t ω ≠ 0}=P {ω | C.process (c^2*t) ω ≠ 0} := by
  obtain ⟨R,he,E,hEm,hEf,hEp⟩ := C.exists_raw_positive_paths hc
  have hs := C.scaled_raw_process_eq hB hc F hw R he E hEm hEf hEp c hcp
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  let A : Set C(ℝ≥0,ℝ) := {p | 0 < R.process (c^2*t) p univ}
  have hAm : MeasurableSet A := measurableSet_lt measurable_const
    ((Measure.measurable_coe MeasurableSet.univ).comp (R.progressive.adapted.measurable (i:=c^2*t)))
  let X := sourceDriverPath B hc
  let Y := sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hc)
  have hXm : Measurable X := source_path_measurable _ hm
  have hYm : Measurable Y := source_path_measurable _ (scaledBrownianDriver_measurable c B hm)
  calc
    _ = P (Y ⁻¹' A) := by
      apply measure_congr
      filter_upwards [hs] with ω hω
      apply propext
      change (C.process t ω ≠ 0) ↔ 0 < scaledRawMass R c B hc t ω univ
      rw [← hω t,Measure.measure_univ_pos,dilationMass_ne_zero_iff]
    _ = (P.map Y) A := (Measure.map_apply hYm hAm).symm
    _ = (P.map X) A := by rw [scaledBrownianDriver_path_law c hcp B hB hm hc]
    _ = P (X ⁻¹' A) := Measure.map_apply hXm hAm
    _ = _ := by
      apply measure_congr
      filter_upwards [he] with ω hω
      apply propext
      change (0 < R.process (c^2*t) (X ω) univ) ↔ C.process (c^2*t) ω ≠ 0
      rw [hω.1 (c^2*t),Measure.measure_univ_pos]

lemma CanonicalMass.nonzero_probability_eq
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    P {ω | C.process s ω ≠ 0}=P {ω | C.process t ω ≠ 0} := by
  have hscale : 0 < NNReal.sqrt (t/s) := NNReal.sqrt_pos.mpr (div_pos ht hs)
  have h := C.nonzero_probability_scaled hB hc F hw (NNReal.sqrt (t/s)) hscale s
  simpa only [NNReal.sq_sqrt,div_mul_cancel₀ _ hs.ne'] using h

lemma CanonicalMass.positive_all_times
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → C.process t ω ≠ 0 :=
  C.positive_all_times_of_scaling hB hc h0 (C.nonzero_probability_eq hB hc F hw)

end SLEExactGauge.Multipoint

end

end OAI

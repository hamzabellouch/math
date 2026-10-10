import OAI.Probability.SLE.Loewner.RawScaleTests
import OAI.Probability.SLE.Geometry.RestartAE
import OAI.Probability.SLE.Mass.RandomRadonEquality

namespace OAI

/-! The raw mass scaling identity survives a scale, time and spatial test
chosen from the stopped past. No uncountable common exceptional set is used. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance randomRawScaleTestsMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance randomRawScaleTestsBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma CanonicalMass.random_raw_scaled_test_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E)
    (hEp : ∀ p∈E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → C(ℝ≥0,ℝ)) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω C(ℝ≥0,ℝ) mΩ (borel _) Y (P.restrict A) =
        P A • @Measure.map Ω C(ℝ≥0,ℝ) mΩ (borel _) (sourceDriverPath B hc) P)
    (c T : Ω → ℝ≥0) (hcM : Measurable[m] c) (hT : Measurable[m] T)
    (hpos : ∀ ω, 0<c ω)
    (f : Ω × upperHalfPlane → ℝ≥0∞) (hf : Measurable[m.prod inferInstance] f) :
    ∀ᵐ ω ∂P,
      (∫⁻ z, f (ω,z) ∂dilationMass κ (c ω) (hpos ω) (R.process (T ω) (Y ω))) =
        ∫⁻ z, f (ω,z) ∂(R.process ((c ω)^2*T ω) (scaleDriverPath (c ω) (Y ω))) := by
  let : MeasurableSpace Ω := mΩ
  have hbp : Measurable (sourceDriverPath B hc) := source_path_measurable _
    (fun s => hBm.comp (measurable_const.prodMk measurable_id))
  let : IsProbabilityMeasure (P.map (sourceDriverPath B hc)) :=
    (Measure.isProbabilityMeasure_map_iff hbp.aemeasurable).mpr inferInstance
  let μ : Ω × C(ℝ≥0,ℝ) → Measure upperHalfPlane :=
    fun p => R.process (T p.1) p.2
  have hμ : @Measurable (Ω × C(ℝ≥0,ℝ)) _ (m.prod (borel _)) _ μ := by
    let : MeasurableSpace Ω := m
    exact _root_.OAI.MeasureTheory.IsProgressive.parameter_time_measurable R.progressive Prod.snd measurable_snd
      (fun p => T p.1) (hT.comp measurable_fst)
  have hμfin (p : Ω × C(ℝ≥0,ℝ)) : IsFiniteMeasureOnCompacts (μ p) := (R.radon _ _).2
  have hleftM := @dilationMass_measurable_family (Ω × C(ℝ≥0,ℝ)) (m.prod (borel _))
    κ (fun p => c p.1) (hcM.comp measurable_fst) (fun p => hpos p.1) μ hμ hμfin
  have hrightM := @RawCanonicalMass.scaled_parameter_measurable (Ω × C(ℝ≥0,ℝ))
    (m.prod (borel _)) R (fun p => c p.1) (fun p => T p.1)
    (hcM.comp measurable_fst) (hT.comp measurable_fst) Prod.snd measurable_snd
  let g : (Ω × C(ℝ≥0,ℝ)) × upperHalfPlane → ℝ≥0∞ := fun p => f (p.1.1,p.2)
  have hg : @Measurable _ _ ((m.prod (borel C(ℝ≥0,ℝ))).prod inferInstance) _ g :=
    hf.comp (measurable_fst.fst.prodMk measurable_snd)
  have hleft := @halfPlane_random_test_measurable (Ω × C(ℝ≥0,ℝ)) (m.prod (borel _)) _ hleftM (fun p => by
    let := hμfin p
    exact (conformalMass_radon _ _ (μ p)).2) g hg
  have hright := @halfPlane_random_test_measurable (Ω × C(ℝ≥0,ℝ)) (m.prod (borel _)) _ hrightM
    (fun p => (R.radon _ _).2) g hg
  exact @restart_ae_random_test Ω C(ℝ≥0,ℝ) mΩ (borel _) P inferInstance (P.map (sourceDriverPath B hc)) inferInstance m hm Y hY hlaw
    _ (measurableSet_eq_fun hleft hright)
    (fun ω => C.raw_scaled_test_eq hB hc F hw R he E hE hEf hEp
      (c ω) (hpos ω) (T ω) (fun z => f (ω,z))
      (hf.comp (measurable_const.prodMk measurable_id)))

lemma CanonicalMass.random_raw_scaled_mass_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E)
    (hEp : ∀ p∈E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → C(ℝ≥0,ℝ)) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω C(ℝ≥0,ℝ) mΩ (borel _) Y (P.restrict A) =
        P A • @Measure.map Ω C(ℝ≥0,ℝ) mΩ (borel _) (sourceDriverPath B hc) P)
    (c T : Ω → ℝ≥0) (hcM : Measurable[m] c) (hT : Measurable[m] T)
    (hpos : ∀ ω, 0<c ω) :
    ∀ᵐ ω ∂P, dilationMass κ (c ω) (hpos ω) (R.process (T ω) (Y ω)) =
      R.process ((c ω)^2*T ω) (scaleDriverPath (c ω) (Y ω)) := by
  let : MeasurableSpace Ω := mΩ
  apply random_halfPlane_measure_eq_of_lintegrals P
    (fun ω => dilationMass κ (c ω) (hpos ω) (R.process (T ω) (Y ω)))
    (fun ω => R.process ((c ω)^2*T ω) (scaleDriverPath (c ω) (Y ω)))
  · intro ω
    let := (R.radon (T ω) (Y ω)).2
    exact (conformalMass_radon _ _ _).1
  · intro ω
    exact (R.radon _ _).1
  · intro f hf
    exact C.random_raw_scaled_test_eq hB hc F hw R he E hE hEf hEp m hm Y hY hlaw
      c T hcM hT hpos (fun p => ENNReal.ofReal (f p.2))
      (f.continuous.measurable.ennreal_ofReal.comp measurable_snd)

end SLEExactGauge.Multipoint

end

end OAI

import OAI.Probability.SLE.Geometry.CanonicalDiskTails
import OAI.Probability.SLE.Gauge.CanonicalDenseSections
import OAI.Probability.SLE.Geometry.ProductDensity

namespace OAI

/-! The disk variable on raw driver space has exactly the finite centered
law used in the prescribed moment coefficients and tail budget. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance rawDiskRadiusMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawDiskRadiusBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def RawCanonicalMass.diskAtRadius (R : RawCanonicalMass) (κ θ u : ℝ)
    (p : C(ℝ≥0,ℝ)) : ℝ :=
  (diskMassValue κ θ (extendedCanonicalMass R.process R.terminal
    (canonicalRadiusLevel κ (u,Target.diskMapInv θ 0,p)) p)).toReal

lemma RawCanonicalMass.diskAtRadius_nonneg (R : RawCanonicalMass) (κ θ u : ℝ)
    (p : C(ℝ≥0,ℝ)) : 0 ≤ R.diskAtRadius κ θ u p := ENNReal.toReal_nonneg

lemma RawCanonicalMass.diskAtRadius_measurable
    {Ξ : Type*} [MeasurableSpace Ξ] (R : RawCanonicalMass) (κ : ℝ)
    (θ u : Ξ → ℝ) (hθ : Measurable θ) (hu : Measurable u)
    (Y : Ξ → C(ℝ≥0,ℝ)) (hY : Measurable Y) :
    Measurable (fun x => R.diskAtRadius κ (θ x) (u x) (Y x)) := by
  have hz : Measurable (fun x => Target.diskMapInv (θ x) 0) := by
    unfold Target.diskMapInv
    fun_prop
  exact (R.disk_at_parameter_measurable κ θ hθ Y hY _
    (measurable_canonicalRadiusLevel_random_state κ hY hu hz)).ennreal_toReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)
  (hc : ∀ ω, Continuous (fun t => B t ω))
  (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (R : RawCanonicalMass)
  (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
    R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)

include C hc F hw R he in
lemma CanonicalMass.raw_diskAtRadius_eq :
    ∀ᵐ ω ∂P, ∀ θ u : ℝ, 0 ≤ u →
      R.diskAtRadius κ θ u (sourceDriverPath B hc ω)=C.diskAtRadius θ u ω := by
  filter_upwards [he] with ω hω
  intro θ u hu
  unfold RawCanonicalMass.diskAtRadius CanonicalMass.diskAtRadius
  rw [canonicalRadiusLevel_eq κ (sourceDriverPath B hc ω) (hw ω) u hu]
  unfold CanonicalMass.atTime extendedCanonicalMass
  split_ifs <;> simp only [hω.1,hω.2]

include C hc F hw R he in
lemma CanonicalMass.raw_diskAtRadius_finiteCentered_tail [SFinite P]
    (θ u b : ℝ) (hu : 0 ≤ u) :
    ((P.map (sourceDriverPath B hc)).withDensity
      (fun p => canonicalFiniteDensity κ (u,Target.diskMapInv θ 0,p)))
      {p | b ≤ R.diskAtRadius κ θ u p} =
      finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) u
        {ω | b ≤ C.diskAtRadius θ u ω} := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  rw [← canonical_finiteCenteredLaw_map P κ B hm hc γ G F (Eventually.of_forall hw) u hu]
  have hA : MeasurableSet {p | b ≤ R.diskAtRadius κ θ u p} := by
    exact measurableSet_le measurable_const
      (R.diskAtRadius_measurable κ (fun _ => θ) (fun _ => u)
        measurable_const measurable_const id measurable_id)
  rw [Measure.map_apply (source_path_measurable _ hm) hA]
  apply measure_congr
  have habs : (finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) u).AbsolutelyContinuous P :=
    withDensity_absolutelyContinuous P _
  filter_upwards [habs.ae_le (C.raw_diskAtRadius_eq hc F hw R he)] with ω hω
  exact propext (by rw [mem_preimage,mem_ofPred_eq,hω θ u hu])

end SLEExactGauge.Multipoint

namespace SLEExactGauge
local instance rawCenteredDiskMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawCenteredDiskBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def rawCenteredDiskLaw (ν : Measure C(ℝ≥0,ℝ)) (κ u : ℝ) : Measure (ℝ × C(ℝ≥0,ℝ)) :=
  ((Target.angleLaw κ).prod ν).withDensity
    (fun p => canonicalFiniteDensity κ (u,Target.diskMapInv p.1 0,p.2))

lemma rawCenteredDiskLaw_lintegral
    (ν : Measure C(ℝ≥0,ℝ)) [SFinite ν] (κ : ℝ) (hκ : 0 < κ) (u : ℝ)
    (f : ℝ × C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂rawCenteredDiskLaw ν κ u) =
      ∫⁻ θ, ∫⁻ p, f (θ,p) ∂ν.withDensity
        (fun p => canonicalFiniteDensity κ (u,Target.diskMapInv θ 0,p)) ∂Target.angleLaw κ := by
  let : IsProbabilityMeasure (Target.angleLaw κ) := Target.angleLaw_isProbability hκ
  have hd : Measurable (fun p : ℝ × C(ℝ≥0,ℝ) =>
      canonicalFiniteDensity κ (u,Target.diskMapInv p.1 0,p.2)) := by
    apply (canonicalFiniteDensity_measurable κ).comp
    apply measurable_const.prodMk
    apply Measurable.prodMk
    · unfold Target.diskMapInv
      fun_prop
    · exact measurable_snd
  exact product_withDensity_lintegral (Target.angleLaw κ) ν _ hd f hf


namespace Multipoint.CanonicalMass
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

lemma raw_centeredDiskTail_eq
    (C : CanonicalMass P κ B hBm γ G)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (u b : ℝ) (hu : 0 ≤ u) :
    rawCenteredDiskLaw (P.map (sourceDriverPath B hc)) κ u
      {p | b ≤ R.diskAtRadius κ p.1 u p.2} = C.centeredDiskTail hc b u := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  let : IsProbabilityMeasure (P.map (sourceDriverPath B hc)) :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  rw [measure_joint_tail_of_lintegral _ (Target.angleLaw κ)
    (fun θ => (P.map (sourceDriverPath B hc)).withDensity
      (fun p => canonicalFiniteDensity κ (u,Target.diskMapInv θ 0,p)))
    (rawCenteredDiskLaw_lintegral _ κ hκ u) _
    (R.diskAtRadius_measurable κ Prod.fst (fun _ => u) measurable_fst measurable_const
      Prod.snd measurable_snd) b,
    C.centeredDiskTail_eq_integral hc hκ F hw b u hu]
  apply lintegral_congr
  intro θ
  exact C.raw_diskAtRadius_finiteCentered_tail hc F hw R he θ u b hu

end Multipoint.CanonicalMass
end SLEExactGauge

end

end OAI

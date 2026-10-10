import OAI.Probability.SLE.Mass.LevelCurrentLimit
import OAI.Probability.SLE.Mass.RadonTestFamily
import OAI.Probability.SLE.Geometry.SpatialPastKernels

namespace OAI

/-! The actual killed Green measure vanishes off the surviving domain and
is almost surely locally finite, as follows from its initial-Green mean bound. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma halfPlaneGreenMeasure_off_surviving
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) :
    halfPlaneGreenMeasure κ B γ G t ω {z : upperHalfPlane | (z : ℂ) ∉ survivingDomain (γ ω) t} = 0 := by
  have hA : MeasurableSet {z : upperHalfPlane | (z : ℂ) ∉ survivingDomain (γ ω) t} :=
    ((isOpen_survivingDomain hw.1 t).preimage continuous_subtype_val).measurableSet.compl
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  rw [halfPlaneGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI]
  apply setLIntegral_eq_zero hAI
  rintro z ⟨x,hx,rfl⟩
  simp only [greenDensity,ite_eq_right hx,ENNReal.ofReal_zero,Pi.zero_apply]

lemma ae_halfPlaneGreenMeasure_compact_finite
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (K : Set upperHalfPlane) (hK : IsCompact K) :
    ∀ᵐ ω ∂P, halfPlaneGreenMeasure κ B γ G t ω K < ⊤ := by
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hb := halfPlaneGreenMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw t univ K
  rw [Measure.restrict_univ,Measure.bind_apply hK.measurableSet
    (halfPlaneGreenMeasure_measurable hBm hBc κ γ G F hw t).aemeasurable] at hb
  exact ae_lt_top ((Measure.measurable_coe hK.measurableSet).comp
    (halfPlaneGreenMeasure_measurable hBm hBc κ γ G F hw t))
    (lt_of_le_of_lt hb hK.measure_lt_top).ne

theorem ae_halfPlaneGreenMeasure_finite_on_compacts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) : ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (halfPlaneGreenMeasure κ B γ G t ω) := by
  let D := localTestFamily upperHalfPlane
  have ha (n : ℕ) := ae_halfPlaneGreenMeasure_compact_finite hB hBm hBc hB0 hκ hκ8 γ G F hw
    t (D.compactSet n) (D.isCompact n)
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  constructor
  intro K hK
  obtain ⟨n,hn⟩ := D.exhaustive K hK
  exact lt_of_le_of_lt (measure_mono hn) (hω n)

end SLEExactGauge.Multipoint

end

end OAI

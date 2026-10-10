import OAI.Probability.SLE.Mass.CanonicalMassConstruction

namespace OAI

/-! Compact restrictions of half-plane measures, viewed as physical measures.
These preserve measurable dependence and compact finiteness. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

/-- The physical measure carried by a fixed compact part of the half-plane. -/
def compactSpatialMass (μ : Measure upperHalfPlane) (K : Set upperHalfPlane) : Measure ℂ :=
  (μ.restrict K).map (Subtype.val : upperHalfPlane → ℂ)

lemma compactSpatialMass_apply (μ : Measure upperHalfPlane) (K : Set upperHalfPlane)
    (A : Set ℂ) (hA : MeasurableSet A) :
    compactSpatialMass μ K A = μ (K ∩ Subtype.val ⁻¹' A) := by
  rw [compactSpatialMass,Measure.map_apply measurable_subtype_coe hA,
    Measure.restrict_apply (hA.preimage measurable_subtype_coe),inter_comm]

lemma compactSpatialMass_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (K : Set upperHalfPlane) (hK : MeasurableSet K) :
    Measurable (fun ω => compactSpatialMass (μ ω) K) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [compactSpatialMass_apply _ _ _ hA]
  exact (Measure.measurable_coe (hK.inter (hA.preimage measurable_subtype_coe))).comp hμ

lemma compactSpatialMass_finite (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ]
    (K : Set upperHalfPlane) (hK : IsCompact K) : IsFiniteMeasure (compactSpatialMass μ K) := by
  constructor
  rw [compactSpatialMass_apply _ _ _ MeasurableSet.univ]
  simpa only [preimage_univ,inter_univ] using hK.measure_lt_top

lemma compactSpatialMass_compact_cell (K : Set upperHalfPlane) (hK : IsCompact K)
    (z : ℂ) (r : ℝ) : IsCompact (K ∩ Subtype.val ⁻¹' closedBall z r) :=
  hK.inter_right (isClosed_closedBall.preimage continuous_subtype_val)

namespace Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma compact_spatial_terminal_measurable (K : Set upperHalfPlane) (hK : IsCompact K) :
    Measurable (fun ω => compactSpatialMass (C.rational.terminal ω) K) :=
  compactSpatialMass_measurable _ C.rational.terminal_measurable K hK.measurableSet

lemma compact_spatial_terminal_finite (K : Set upperHalfPlane) (hK : IsCompact K) (ω : Ω) :
    IsFiniteMeasure (compactSpatialMass (C.rational.terminal ω) K) := by
  let := (C.rational.terminal_radon ω).2
  exact compactSpatialMass_finite _ K hK

lemma compact_spatial_initial_finite (K : Set upperHalfPlane) (hK : IsCompact K) :
    IsFiniteMeasure (compactSpatialMass (initialGreenMeasure κ) K) := by
  let := initialGreenMeasure_finite_on_compacts κ
  exact compactSpatialMass_finite _ K hK

lemma compact_spatial_terminal_mean (K : Set upperHalfPlane) (hK : IsCompact K)
    (A : Set ℂ) (hA : MeasurableSet A) :
    (∫⁻ ω, compactSpatialMass (C.rational.terminal ω) K A ∂P) =
      compactSpatialMass (initialGreenMeasure κ) K A := by
  simp_rw [compactSpatialMass_apply _ _ _ hA]
  rw [← Measure.bind_apply (hK.measurableSet.inter (hA.preimage measurable_subtype_coe))
    C.rational.terminal_measurable.aemeasurable,C.rational.mean]

end Multipoint.CanonicalMass
end SLEExactGauge

end

end OAI

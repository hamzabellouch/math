import OAI.Probability.SLE.Geometry.CompactCellTail
import OAI.Probability.SLE.Geometry.CanonicalLowerSegments

namespace OAI

/-! A canonical angle mixing inequality implies the prescribed-gauge
Hausdorff lower bound. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance lowerAngleMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance lowerAngleBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance lowerAngleLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

theorem CanonicalMass.compact_positive_prescribed_of_canonical_angle_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0 < κ) (hκ8 : κ < 8)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (D : Set C(ℝ≥0,ℝ)) (hD : MeasurableSet D)
    (hDf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈D)
    (hDp : ∀ p∈D, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (δ : ℝ) (hδ : 0<δ)
    (hangle : ∀ v : ℝ, δ≤v → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∀ θ∈Ioo (0:ℝ) Real.pi, canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f θ ≤
        2*(∫⁻ φ, f φ ∂Target.angleLaw κ))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    ∀ᵐ ω ∂P, ∀ E : Set ℂ, MeasurableSet E →
      0<C.rational.terminal ω (K∩Subtype.val ⁻¹' E) →
      0<Target.hausdorff (Target.gauge κ W) E := by
  obtain ⟨N,hN⟩ := Target.eventually_entryPhysicalLevel_large_on_compact hκ W
    (by positivity : 0<4096*Real.pi) δ K hK
  apply C.ae_positive_prescribed_of_late_disk_tails hB hc h0 hκ hκ8 F hw hpublished
    hgrowth W hW (fun n : ℕ => (n:ℝ)) (fun n => Nat.cast_nonneg n)
    (fun _ _ h => Nat.cast_le.mpr h) tendsto_natCast_atTop_atTop
    (TopologicalSpace.denseSeq ℝ≥0) (TopologicalSpace.denseRange_denseSeq ℝ≥0)
    K hK (16*(65536*Real.pi)^dimension κ) (by positivity) N
  intro e heN i j
  obtain ⟨M,hM⟩ := Target.entryPhysicalLevel_bounded_on_compact κ W e.val
    (by positivity : 0<4096*Real.pi) K hK
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop M)] with n hn
  apply C.compact_cell_tail_of_angle_bound hB hc h0 hκ hκ8 F hw R he
    D hD hDf hDp hgrowth hpublished W e δ hδ hangle
    (prescribedCompactGridCell κ W K e i)
    (compactSpatialMass_compact_cell K hK _ _)
    (coverGridCenter (Target.radii κ W e) i)
  · rintro _ ⟨z,hz,rfl⟩
    exact hz.2
  · intro z hz
    exact (hN e heN z hz.1).le
  · intro z hz
    exact (hM z hz.1).trans_lt hn

theorem CanonicalMass.positive_prescribed_all_segments_of_canonical_angle_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0 < κ) (hκ8 : κ < 8)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (D : Set C(ℝ≥0,ℝ)) (hD : MeasurableSet D)
    (hDf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈D)
    (hDp : ∀ p∈D, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (δ : ℝ) (hδ : 0<δ)
    (hangle : ∀ v : ℝ, δ≤v → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∀ θ∈Ioo (0:ℝ) Real.pi, canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f θ ≤
        2*(∫⁻ φ, f φ ∂Target.angleLaw κ))
    : ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s<t →
      0<Target.hausdorff (Target.gauge κ W) (γ ω '' Icc s t) := by
  apply C.positive_all_segments_of_compact_lower hB hc h0 hκ F hw hpublished
    (Target.gauge κ W)
  intro n
  exact C.compact_positive_prescribed_of_canonical_angle_bound hB hc h0 hκ hκ8
    F hw R he D hD hDf hDp hgrowth hpublished W hW δ hδ hangle
    (compactCovering upperHalfPlane n) (isCompact_compactCovering _ _)

end SLEExactGauge.Multipoint

end

end OAI

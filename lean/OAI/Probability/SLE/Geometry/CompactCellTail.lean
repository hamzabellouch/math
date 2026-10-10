import OAI.Probability.SLE.Gauge.PrescribedCellNormalization
import OAI.Probability.SLE.Mass.CompactEntryLevels
import OAI.Probability.SLE.Gauge.CanonicalLateGridLower

namespace OAI

/-! The actual finite centered cell bounds, integrated over a compact
spatial cell, supply the late-grid hypothesis for the prescribed gauge. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance compactCellTailMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance compactCellTailBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.compact_cell_tail_of_angle_bound
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
    (W : Target.WienerLaw) (e : Target.GaugeIndex κ W)
    (δ : ℝ) (hδ : 0<δ)
    (hangle : ∀ v : ℝ, δ≤v → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∀ θ∈Ioo (0:ℝ) Real.pi, canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f θ ≤
        2*(∫⁻ φ, f φ ∂Target.angleLaw κ))
    (K : Set upperHalfPlane) (hK : IsCompact K) (c : ℂ)
    (hKball : (Subtype.val : upperHalfPlane → ℂ) '' K ⊆
      closedBall c (2*Target.radii κ W e))
    (V : ℝ)
    (hbase : ∀ z∈K, δ≤Target.entryPhysicalLevel κ W e.val (4096*Real.pi) z)
    (hV : ∀ z∈K, Target.entryPhysicalLevel κ W e.val (4096*Real.pi) z<V)
    (J : Finset ℝ≥0) :
    C.compactFinitePastTest K
      ((16*(65536*Real.pi)^dimension κ)*Target.weights κ W e*(Target.radii κ W e)^Target.d κ)
      J V ≤ (2*C.limitingDiskTail hc (16*Target.weights κ W e))*initialGreenMeasure κ K := by
  let L : Set ℂ := (Subtype.val : upperHalfPlane → ℂ) '' K
  have hL : MeasurableSet L := (hK.image continuous_subtype_val).measurableSet
  have hpre : Subtype.val ⁻¹' L = K := Subtype.val_injective.preimage_image K
  have ht : C.limitingDiskTail hc (16*Target.weights κ W e) ≠ ∞ :=
    ne_top_of_le_ne_top (by norm_num) (C.limitingDiskTail_le_one hB hc hκ hκ8 F hw _)
  rw [initialGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hL,← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ht)]
  apply setLIntegral_mono' hL
  rintro x ⟨z,hz,rfl⟩
  let u := Target.entryPhysicalLevel κ W e.val (4096*Real.pi) (z:ℂ)
  have hu : 0<u := hδ.trans_le (hbase z hz)
  have hv : 0<V-u := sub_pos.mpr (hV z hz)
  have hr := Target.radii_pos κ W e
  have hball : L⊆closedBall (z:ℂ) (2*(2*Target.radii κ W e)) :=
    cell_subset_ball_at_member hKball ⟨z,hz,rfl⟩
  have hh := C.centered_strict_past_cell_tail_of_angle_bound hB hc h0 hκ hκ8 F hw
    R he D hD hDf hDp hgrowth hpublished (z:ℂ) z.property u (V-u)
    (2*Target.radii κ W e) (16*Target.weights κ W e) hu hv (by positivity)
    (prescribed_lower_radius κ W e.val z.property) L hL hball
    (hangle u (hbase z hz) _ (R.angleDiskTail_measurable _ _ _ _)) J
  rw [show u+(V-u)=V by ring,hpre,
    prescribed_lower_threshold κ (Target.radii κ W e) (Target.weights κ W e) hr] at hh
  exact (mul_le_mul' le_rfl hh).trans_eq (mul_comm _ _)

end SLEExactGauge.Multipoint

end

end OAI

import OAI.Probability.SLE.Gauge.PrescribedBatchMixing
import OAI.Probability.SLE.Angle.RadiusAngleBounds

namespace OAI

/-! A canonical angle transition bound across the reserved preceding gaps
implies the exact prescribed batch estimate. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance canonicalBatchMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance canonicalBatchBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.prescribed_batch_failure_of_canonical_angle_bound
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
    {n J : ℕ} (hn : 3≤n) (e : Fin J → ℤ×ℕ) (hi : Function.Injective e)
    (he' : ∀ kj, kj∈range e ↔ kj.2 < Target.multiplicity κ W n kj.1)
    (horder : StrictMono (fun i => Target.entryPosition κ W (n,some (e i))))
    (z : ℂ) (hz : z∈upperHalfPlane)
    (hl : ∀ o, 0 ≤ Target.entryPhysicalLevel κ W (n,o) (2048*Real.pi) z)
    (δ : ℝ) (hδ : 0<δ)
    (hgap : ∀ i : Fin J, Target.prescribedTestPastLevel κ W n e (2048*Real.pi) z i.val+δ ≤
      Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi) z)
    (hangle : ∀ (v : ℝ), δ≤v → ∀ (f : ℝ → ℝ≥0∞), Measurable f →
      ∀ θ∈Ioo (0:ℝ) Real.pi, (∫⁻ φ, f φ ∂Target.angleLaw κ)/2 ≤
        canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f θ) :
    C.prescribedCenteredFailure W n e (4096*Real.pi) ((128*Real.pi)^dimension κ) z ≤
      ENNReal.ofReal (Real.exp (-((2:ℝ)^n/16))) := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let ν := P.map (sourceDriverPath B hc)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  have hm1 := C.moment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW 1
  have hJn := C.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n
  have hei (i : Fin J) : (e i).2 < Target.multiplicity κ W n (e i).1 := (he' _).mp ⟨i,rfl⟩
  apply C.prescribed_batch_failure_of_angle_mixing hB hc h0 hκ hκ8 F hw R he D hD hDf hDp
    hgrowth hpublished W hW hn e hi he' horder z hz hl
  intro i E hE
  let s := Target.prescribedTestPastLevel κ W n e (2048*Real.pi) z i.val
  let u := Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi) z
  let V := Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi) z
  let f := R.angleDiskTail ν κ (Target.entryValue (n,some (e i)))
    (2*Target.a κ*(Target.batchLevel κ W n:ℝ))
  have hs : 0 ≤ s := Target.prescribedTestPastLevel_nonneg hκ W n e (2048*Real.pi) z hl i.val
  have hsu : δ ≤ u-s := by have hh := hgap i; dsimp only [s,u]; linarith
  have huV : u≤V := by
    have hend := Target.prescribedBatchLevel_test_end_le_cleanup hκ W (by omega) hm1 hJn e hei
      (2048*Real.pi) z i
    have ha := Target.internal_a_pos hκ
    have hnon1 : 0≤2*Target.a κ*(Target.batchLevel κ W n:ℝ) := by positivity
    have hnon2 : 0≤2*Target.a κ*(n:ℝ) := by positivity
    dsimp only [u,V]
    linarith
  have hf : Measurable f := R.angleDiskTail_measurable ν κ _ _
  have hb := (radius_angle_average_bounds hB hBm hc h0 hκ hκ8 γ G F hw hpublished
    z hz s (u-s) V hs (hδ.trans_le hsu) (by linarith) f hf
    ((∫⁻ φ, f φ ∂Target.angleLaw κ)/2) ∞
    (fun θ hθ => ⟨hangle (u-s) hsu f hf θ hθ,le_top⟩) E hE).1
  have heq : s+(u-s)=u := by ring
  simpa only [heq] using hb

end SLEExactGauge.Multipoint

end

end OAI

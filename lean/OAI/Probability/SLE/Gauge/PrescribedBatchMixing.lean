import OAI.Probability.SLE.Gauge.PrescribedEntryKernel
import OAI.Probability.SLE.Gauge.PrescribedAdaptedBatch
import OAI.Probability.SLE.Geometry.CanonicalInteriorBound

namespace OAI

/-! Angular mixing on the gaps preceding the tests combines with the exact
normalized disk kernel to give the prescribed batch estimate. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance mixingBatchMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance mixingBatchBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.prescribed_batch_failure_of_angle_mixing
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
    (hmix : ∀ (i : Fin J) (E : Set Ω),
      MeasurableSet[(actual_radiusLevelTime_stopping hB
        (fun t => (hBm.of_uncurry_left : Measurable (B t))) hBm hc h0
        κ hκ hκ8 γ G F hw z hz (Target.prescribedTestPastLevel κ W n e (2048*Real.pi) z i.val)
        (Target.prescribedTestPastLevel_nonneg hκ W n e (2048*Real.pi) z hl i.val)).measurableSpace] E →
      ((∫⁻ θ, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ (Target.entryValue (n,some (e i)))
          (2*Target.a κ*(Target.batchLevel κ W n:ℝ)) θ ∂Target.angleLaw κ)/2)*
        finiteCenteredLaw P κ B γ G z (Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi) z) E ≤
      ∫⁻ ω in E, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ (Target.entryValue (n,some (e i)))
        (2*Target.a κ*(Target.batchLevel κ W n:ℝ))
        (extendedMarkedAngle κ B γ G (fun ω => radiusLevelTime (γ ω) (G ω) z
          (Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi) z)) z ω)
        ∂finiteCenteredLaw P κ B γ G z (Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi) z)) :
    C.prescribedCenteredFailure W n e (4096*Real.pi) ((128*Real.pi)^dimension κ) z ≤
      ENNReal.ofReal (Real.exp (-((2:ℝ)^n/16))) := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let : IsProbabilityMeasure (P.map (sourceDriverPath B hc)) :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  have hm1 := C.moment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW 1
  have hJn := C.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n
  have hei (i : Fin J) : (e i).2 < Target.multiplicity κ W n (e i).1 := (he' _).mp ⟨i,rfl⟩
  have ha := Target.internal_a_pos hκ
  have hd : 2*Target.a κ*(Target.batchLevel κ W n:ℝ)=4*(Target.batchLevel κ W n:ℝ)/κ := by
    unfold Target.a
    ring
  have hv : 0 ≤ 4*(Target.batchLevel κ W n:ℝ)/κ := by positivity
  let : IsProbabilityMeasure (centeredDiskLaw P κ B hc (4*(Target.batchLevel κ W n:ℝ)/κ)) :=
    centeredDiskLaw_isProbability hB hBm hc hκ hκ8 γ G F hw _ hv
  apply C.prescribed_adapted_batch_failure hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW
    hn e hi he' horder (4096*Real.pi) ((128*Real.pi)^dimension κ) (2048*Real.pi) z hz hl
    _ (hl none)
  intro i E hE
  have hgap := Target.prescribedTestPastLevel_gap hκ W (by omega) e horder
    (2048*Real.pi) z 0 (fun j => hl (some (e j))) (by positivity) i
  simp only [add_zero] at hgap
  have hS := actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz
    (Target.prescribedTestPastLevel κ W n e (2048*Real.pi) z i.val)
    (Target.prescribedTestPastLevel_nonneg hκ W n e (2048*Real.pi) z hl i.val)
  have hT := actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz
    (Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi) z) (hl _)
  have hET : MeasurableSet[hT.measurableSpace] E :=
    hS.measurableSpace_mono hT (fun ω => radiusLevelTime_mono ((hc ω).const_mul _)
      (hw ω) z (Target.prescribedTestPastLevel_nonneg hκ W n e (2048*Real.pi) z hl i.val) hgap) E hE
  have hend := Target.prescribedBatchLevel_test_end_le_cleanup hκ W (by omega) hm1 hJn e hei
    (2048*Real.pi) z i
  have hV : Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi) z+
      2*Target.a κ*(Target.batchLevel κ W n:ℝ) ≤
        Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi) z := by
    have hn0 : 0 ≤ 2*Target.a κ*(n:ℝ) := by positivity
    linarith
  have htest := C.prescribed_entry_success_kernel hB hc h0 hκ hκ8 F hw R he D hD hDf hDp
    hgrowth hpublished W n (e i) z hz (hl _) _ hV E hET
  have hav := R.angleDiskTail_average (P.map (sourceDriverPath B hc)) κ hκ
    (Target.entryValue (n,some (e i))) (2*Target.a κ*(Target.batchLevel κ W n:ℝ))
  rw [C.raw_centeredDiskTail_eq hc hκ F hw R he _ _ (by positivity),hd] at hav
  have hhalf : ENNReal.ofReal
      ((centeredDiskLaw P κ B hc (4*(Target.batchLevel κ W n:ℝ)/κ)).real
        {p | MomentBatches.dyadic (e i).1 ≤ C.diskAtRadius p.1 (4*(Target.batchLevel κ W n:ℝ)/κ) p.2}/2) =
      (∫⁻ θ, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ (Target.entryValue (n,some (e i)))
          (2*Target.a κ*(Target.batchLevel κ W n:ℝ)) θ ∂Target.angleLaw κ)/2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num),ofReal_measureReal,hd,hav]
    rcases e i with ⟨k,j⟩
    norm_num [CanonicalMass.centeredDiskTail,Target.entryValue,MomentBatches.dyadic]
  rw [hhalf]
  exact (hmix i E hE).trans htest

end SLEExactGauge.Multipoint

end

end OAI

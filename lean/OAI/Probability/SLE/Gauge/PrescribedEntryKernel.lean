import OAI.Probability.SLE.Gauge.PrescribedRadiusFinalLaw
import OAI.Probability.SLE.Gauge.PrescribedRadiusLevels

namespace OAI

/-! The physical radius, exact prescribed inner-clock duration, threshold,
and normalized angle kernel of one entry all agree with the batch test. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance entryKernelMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance entryKernelBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma prescribed_ball_threshold (κ r b : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*ENNReal.ofReal b =
      ENNReal.ofReal ((128*Real.pi)^dimension κ*b*r^Target.d κ) := by
  have hd : Target.d κ=dimension κ := by rw [Target.dimension_eq]; rfl
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
    Real.mul_rpow (by positivity : 0 ≤ 128*Real.pi) hr.le,hd]
  congr 1
  ring

theorem CanonicalMass.prescribed_entry_success_kernel
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
    (W : Target.WienerLaw) (n : ℕ) (e : ℤ×ℕ) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ Target.entryPhysicalLevel κ W (n,some e) (2048*Real.pi) z)
    (V : ℝ) (hV : Target.entryPhysicalLevel κ W (n,some e) (2048*Real.pi) z+
      2*Target.a κ*(Target.batchLevel κ W n:ℝ) ≤ V) :
    ∀ A : Set Ω, MeasurableSet[(actual_radiusLevelTime_stopping hB
      (fun t => (hBm.of_uncurry_left : Measurable (B t))) hBm hc h0
      κ hκ hκ8 γ G F hw z hz _ hu).measurableSpace] A →
      (∫⁻ ω in A, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ (Target.entryValue (n,some e))
        (2*Target.a κ*(Target.batchLevel κ W n:ℝ))
        (extendedMarkedAngle κ B γ G (fun ω => radiusLevelTime (γ ω) (G ω) z
          (Target.entryPhysicalLevel κ W (n,some e) (2048*Real.pi) z)) z ω)
        ∂finiteCenteredLaw P κ B γ G z V) ≤
      finiteCenteredLaw P κ B γ G z V
        (A∩C.prescribedBallTest (fun ω => radiusLevelTime (γ ω) (G ω) z
          (Target.entryPhysicalLevel κ W (n,some e) (2048*Real.pi) z+
            2*Target.a κ*(Target.batchLevel κ W n:ℝ)))
          z ((4096*Real.pi)*Target.entryRadius κ W (n,some e))
          (ENNReal.ofReal ((128*Real.pi)^dimension κ*Target.entryValue (n,some e)*
            (Target.entryRadius κ W (n,some e))^Target.d κ))) := by
  have hr : 0 < Target.entryRadius κ W (n,some e) := Real.exp_pos _
  have hℓ : (0:ℝ)<Target.batchLevel κ W n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Target.batchLevel_ge_one κ W n))
  have hv : 0 < 2*Target.a κ*(Target.batchLevel κ W n:ℝ) := by
    exact mul_pos (mul_pos (by norm_num) (Target.internal_a_pos hκ)) hℓ
  intro A hA
  have h := C.prescribed_disk_test_under_final_law hB hc h0 hκ hκ8 F hw R he D hD hDf hDp
    hgrowth hpublished z hz (Target.entryPhysicalLevel κ W (n,some e) (2048*Real.pi) z)
    (2*Target.a κ*(Target.batchLevel κ W n:ℝ)) (Target.entryRadius κ W (n,some e))
    (Target.entryValue (n,some e)) V hu hv hr
    (Target.entryPhysicalLevel_radius κ W (n,some e) (by positivity) hz) hV A hA
  rwa [prescribed_ball_threshold κ _ _ hr] at h

end SLEExactGauge.Multipoint

end

end OAI

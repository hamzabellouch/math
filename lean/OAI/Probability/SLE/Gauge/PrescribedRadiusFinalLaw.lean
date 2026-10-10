import OAI.Probability.SLE.Gauge.PrescribedRadiusTest

namespace OAI

/-! A stopped disk test has the same kernel bound under every later finite
centered law. The terminal cover is not used in this change of measure. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance finalTestMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance finalTestBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.prescribed_disk_test_under_final_law
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
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u v r b V : ℝ)
    (hu : 0 ≤ u) (hv : 0 < v) (hr : 0 < r)
    (hR : (2*z.im)*Real.exp (-u)=(2048*Real.pi)*r) (hV : u+v ≤ V) :
    ∀ A : Set Ω, MeasurableSet[(actual_radiusLevelTime_stopping hB
      (fun t => (hBm.of_uncurry_left : Measurable (B t))) hBm hc h0
      κ hκ hκ8 γ G F hw z hz u hu).measurableSpace] A →
      (∫⁻ ω in A, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
        (extendedMarkedAngle κ B γ G (fun ω => radiusLevelTime (γ ω) (G ω) z u) z ω)
        ∂finiteCenteredLaw P κ B γ G z V) ≤
      finiteCenteredLaw P κ B γ G z V
        (A∩C.prescribedBallTest (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v))
          z ((4096*Real.pi)*r)
          (ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)) := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let σ : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  let T : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)
  have hσ : IsStoppingTime ℱ σ :=
    actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz u hu
  have huv : 0 ≤ u+v := add_nonneg hu hv.le
  have hT : IsStoppingTime ℱ T :=
    actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz (u+v) huv
  have hσT (ω : Ω) : σ ω ≤ T ω :=
    radiusLevelTime_mono ((hc ω).const_mul _) (hw ω) z hu (by linarith)
  let f := fun ω => R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
    (extendedMarkedAngle κ B γ G σ z ω)
  let test := C.prescribedBallTest T z ((4096*Real.pi)*r)
    (ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)
  let Q := finiteCenteredLaw P κ B γ G z (u+v)
  let QV := finiteCenteredLaw P κ B γ G z V
  let : IsProbabilityMeasure (P.map (sourceDriverPath B hc)) :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  have hfm : Measurable[hσ.measurableSpace] f :=
    (R.angleDiskTail_measurable _ κ b v).comp
      (extendedMarkedAngle_measurable B hm hc κ γ G F hw σ hσ z)
  intro A hA
  have hleft : (∫⁻ ω in A, f ω ∂QV)=(∫⁻ ω in A, f ω ∂Q) := by
    have h := @lintegral_eq_of_stopped_events Ω mΩ QV Q hσ.measurableSpace
      hσ.measurableSpace_le (fun E hE =>
        finiteCenteredLaw_consistent_at_extended_stop hB hBm hc h0 κ hκ hκ8 γ G F
          (Eventually.of_forall hw) z hz (u+v) V huv hV σ hσ
          (Eventually.of_forall hσT) E hE) (A.indicator f) (hfm.indicator hA)
    simpa only [lintegral_indicator (hσ.measurableSpace_le _ hA)] using h
  have hAm : MeasurableSet[hT.measurableSpace] A :=
    hσ.measurableSpace_mono hT hσT A hA
  have htest : MeasurableSet[hT.measurableSpace] test :=
    C.prescribedBallTest_measurable T hT _ _ _
  have hright : QV (A∩test)=Q (A∩test) :=
    finiteCenteredLaw_consistent_at_radius_stop hB hBm hc h0 κ hκ hκ8 γ G F
      (Eventually.of_forall hw) z hz (u+v) V huv hV T hT
      (Eventually.of_forall fun _ => rfl) (A∩test) (hAm.inter htest)
  change (∫⁻ ω in A, f ω ∂QV) ≤ QV (A∩test)
  rw [hleft,hright]
  exact C.prescribed_disk_test_at_radius hB hc h0 hκ hκ8 F hw R he D hD hDf hDp
    hgrowth hpublished z hz u v r b hu hv hr hR A hA

end SLEExactGauge.Multipoint

end

end OAI

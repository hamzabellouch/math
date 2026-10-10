import OAI.Probability.SLE.Geometry.NormalizedRadiusCell
import OAI.Probability.SLE.Geometry.NormalizedDiskDensity
import OAI.Probability.SLE.Loewner.RawDiskAngleTail
import OAI.Probability.SLE.Geometry.StoppedMarkedStateMeasurability
import OAI.Probability.SLE.Geometry.FiniteDensityAtRadiusState
import OAI.Probability.SLE.Gauge.PrescribedCanonicalTests
import OAI.Probability.SLE.Geometry.RestartWeightedKernel

namespace OAI

/-! The actual disk test has its finite centered success kernel at the
starting angle. Only finite stopped events enter the change of law. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance diskTestMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance diskTestBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.prescribed_disk_test_kernel
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
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t =>
      (hBm.of_uncurry_left : Measurable (B t)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u v r b : ℝ)
    (hu : 0 ≤ u) (hv : 0 < v) (hr : 0 < r)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (hlive : ∀ ω∈E, z ∈ survivingDomain (γ ω) (τ ω))
    (hbase : ∀ ω∈E, fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u))
    (hR : ∀ ω∈E, fullRadius (G ω) (τ ω) z=(2048*Real.pi)*r) :
    ∃ M : Ω → ℝ≥0∞, Measurable[hτ.measurableSpace] M ∧
      (∀ ω, M ω ≠ ∞) ∧
      (∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
        (∫⁻ ω in A∩E, M ω ∂P)=finiteCenteredLaw P κ B γ G z (u+v) (A∩E)) ∧
      ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
        (∫⁻ ω in A∩E, M ω*R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
          (stoppedMarkedCenter κ B γ G τ z ω).arg ∂P) ≤
        finiteCenteredLaw P κ B γ G z (u+v)
          (A∩E∩C.prescribedBallTest (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v))
            z ((4096*Real.pi)*r)
            (ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)) := by
  classical
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let ν := P.map (sourceDriverPath B hc)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  let a := stoppedMarkedScale κ B γ G τ z
  let θ := fun ω => (stoppedMarkedCenter κ B γ G τ z ω).arg
  let Y := normalizedRestartDriverPath B hc τ a
  have ham : Measurable[hτ.measurableSpace] a :=
    source_stoppedMarkedScale_measurable B hm hc κ γ G F hw τ hτ z
  have ha : ∀ ω, 0 < a ω := stoppedMarkedScale_pos κ B γ G τ z
  have hθm : Measurable[hτ.measurableSpace] θ :=
    (source_stoppedMarkedCenter_measurable B hm hc κ γ G F hw τ hτ z).carg
  have hY : Measurable Y := measurable_scaleDriverPath.comp
    ((ham.mono hτ.measurableSpace_le le_rfl).inv.prodMk
      (sourceRestartDriverPath_measurable B hm hc τ hτ))
  have hYlaw (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
      (P.restrict A).map Y=P A • ν :=
    source_restart_random_scale_driver_law B hB hm hc τ hτ
      (fun ω => (a ω)⁻¹) ham.inv (fun ω => inv_pos.mpr (ha ω)) A hA
  have hpolar (ω : Ω) (hω : ω∈E) :
      θ ω∈Ioo (0:ℝ) Real.pi ∧ G ω (τ ω) z=
        (Real.sqrt κ*B (τ ω) ω:ℝ)+(a ω:ℂ)*Complex.exp (θ ω*Complex.I) := by
    have hh := (hw ω).live_marked_polar (τ ω) z (hlive ω hω)
    simpa only [θ,a,stoppedMarkedCenter_eq κ B γ G τ z ω (hlive ω hω),
      stoppedMarkedScale_eq_on_live B κ γ G F hw τ z ω (hlive ω hω)] using hh.2
  obtain ⟨M,hM,hMf,hMactual,hMpast⟩ := exists_finiteDensity_at_radius_state
    hB hBm hc h0 κ hκ hκ8 γ G F hw τ hτ z hz u v hu hv E hE hlive hbase
  refine ⟨M,hM,hMf,hMpast,?_⟩
  intro A hA
  let T := fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)
  let q := fun ω => R.angleDiskTail ν κ b v (θ ω)
  let test := C.prescribedBallTest T z ((4096*Real.pi)*r)
    (ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)
  let S := E∩test
  let Z := fun ω => ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
    (γ ω) (G ω) z (u+v)/initialGreen κ z)
  let Q : Set (Ω × C(ℝ≥0,ℝ)) := {x | x.1∈E ∧ b ≤ R.diskAtRadius κ (θ x.1) v x.2}
  let K : Ω × C(ℝ≥0,ℝ) → ℝ≥0∞ := fun x =>
    M x.1*canonicalFiniteDensity κ (v,Target.diskMapInv (θ x.1) 0,x.2)
  have hQ : @MeasurableSet _ (hτ.measurableSpace.prod (borel _)) Q :=
    (hE.preimage measurable_fst).inter (measurableSet_le measurable_const
      (@RawCanonicalMass.diskAtRadius_measurable (Ω × C(ℝ≥0,ℝ))
        (hτ.measurableSpace.prod (borel _)) R κ _ _ (hθm.comp measurable_fst)
        measurable_const Prod.snd measurable_snd))
  have hzm : Measurable[hτ.measurableSpace] (fun ω => Target.diskMapInv (θ ω) 0) := by
    unfold Target.diskMapInv
    fun_prop
  have hK : @Measurable _ _ (hτ.measurableSpace.prod (borel _)) _ K :=
    (hM.comp measurable_fst).mul ((canonicalFiniteDensity_measurable κ).comp
      (measurable_const.prodMk ((hzm.comp measurable_fst).prodMk measurable_snd)))
  have hT := actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz
    (u+v) (by linarith)
  have htest : MeasurableSet test := hT.measurableSpace_le _
    (C.prescribedBallTest_measurable T hT _ _ _)
  have hS : MeasurableSet S := (hτ.measurableSpace_le _ hE).inter htest
  have hsec : ∀ᵐ ω ∂P, (1:ℝ≥0∞)*E.indicator (fun ω => M ω*q ω) ω ≤
      ∫⁻ p, Q.indicator K (ω,p) ∂ν := by
    apply Eventually.of_forall
    intro ω
    by_cases hω : ω∈E
    · let H := {p | b ≤ R.diskAtRadius κ (θ ω) v p}
      have hH : MeasurableSet H := measurableSet_le measurable_const
        (R.diskAtRadius_measurable κ (fun _ => θ ω) (fun _ => v)
          measurable_const measurable_const id measurable_id)
      have hid : (fun p => Q.indicator K (ω,p)) =
          (fun p => M ω*H.indicator (fun p => canonicalFiniteDensity κ
            (v,Target.diskMapInv (θ ω) 0,p)) p) := by
        funext p
        by_cases hp : p∈H
        · rw [indicator_of_mem (show (ω,p)∈Q from ⟨hω,hp⟩),indicator_of_mem hp]
        · rw [indicator_of_notMem (show (ω,p)∉Q from fun h => hp h.2),
            indicator_of_notMem hp,mul_zero]
      rw [hid,lintegral_const_mul' _ _ (hMf ω),lintegral_indicator hH,
        ← withDensity_apply _ hH,indicator_of_mem hω,one_mul]
      exact le_rfl
    · rw [indicator_of_notMem hω,mul_zero]
      exact bot_le
  have hden := normalized_restart_disk_density hB hm hc γ G F hw hpublished τ hτ a ham ha
  have hcell := C.normalized_cell_bounds_at_radius hB hc hκ F hw R he D hD hDf hDp
    hgrowth hpublished τ hτ a ham ha
  have hactual : ∀ᵐ ω ∂P, Q.indicator K (ω,Y ω) ≤ S.indicator Z ω := by
    filter_upwards [hden,hcell,hMactual] with ω hd hb hMω
    by_cases hQω : (ω,Y ω)∈Q
    · obtain ⟨hωE,hbval⟩ := hQω
      have hpol := hpolar ω hωE
      have hKZ : K (ω,Y ω)=Z ω := by
        change M ω*canonicalFiniteDensity κ (v,Target.diskMapInv (θ ω) 0,Y ω)=Z ω
        rw [hMω hωE]
        exact (hd _ hpol.1 z (hlive ω hωE) hz hpol.2 u v hu hv (hbase ω hωE)).symm
      rw [indicator_of_mem (show (ω,Y ω)∈Q from ⟨hωE,hbval⟩),hKZ]
      by_cases hf : T ω<⊤
      · have hmass := (hb (θ ω) hpol.1 z (hlive ω hωE) r hr (hR ω hωE)
          hpol.2 u hu (hbase ω hωE) v hv hf).1
        have hvb := (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hbval)).trans hmass
        have heval : extendedCanonicalMass C.process C.rational.terminal (T ω) ω =
            C.process ((T ω).untopD 0) ω := by
          dsimp only [extendedCanonicalMass]
          rw [ite_eq_left hf]
          rfl
        rw [heval] at hvb
        have ht : ω∈test := ⟨hf,hvb⟩
        rw [indicator_of_mem (show ω∈S from ⟨hωE,ht⟩)]
      · have hz0 : Z ω=0 := by
          simp only [Z,stoppedGreen,show ¬radiusLevelTime (γ ω) (G ω) z (u+v)<∞ from hf,
            ite_false,zero_div,ENNReal.ofReal_zero]
        rw [hz0]
        exact bot_le
    · rw [indicator_of_notMem hQω]
      exact bot_le
  have hh := @restart_weighted_event_lower_bound Ω C(ℝ≥0,ℝ) mΩ (borel _)
    P inferInstance ν inferInstance hτ.measurableSpace hτ.measurableSpace_le
    Y hY hYlaw K hK Q hQ (E.indicator (fun ω => M ω*q ω)) Z 1 (by simp) S hS
    hsec hactual A hA
  rw [one_mul,setLIntegral_indicator (hτ.measurableSpace_le _ hE),inter_comm E A] at hh
  simpa only [ν,q,θ,Z,S,test,finiteCenteredLaw,← inter_assoc] using hh

end SLEExactGauge.Multipoint

end

end OAI

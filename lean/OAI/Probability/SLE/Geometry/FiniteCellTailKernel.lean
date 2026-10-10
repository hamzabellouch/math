import OAI.Probability.SLE.Gauge.PrescribedDiskTestKernel
import OAI.Probability.SLE.Gauge.PrescribedDiskConditional

namespace OAI

/-! The upper physical cell comparison gives the reverse test inequality:
a large canonical cell mass forces a large normalized finite disk mass. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance cellKernelMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance cellKernelBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def CanonicalMass.finiteCellMassTest
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G) (S : Ω → WithTop ℝ≥0)
    (K : Set ℂ) (b : ℝ≥0∞) : Set Ω :=
  finiteStoppedThreshold (fun t ω => C.process t ω (Subtype.val ⁻¹' K)) S b

lemma CanonicalMass.finiteCellMassTest_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G) (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun t =>
      (hBm.of_uncurry_left : Measurable (B t)).stronglyMeasurable)) S)
    (K : Set ℂ) (hK : MeasurableSet K) (b : ℝ≥0∞) :
    MeasurableSet[hS.measurableSpace] (C.finiteCellMassTest S K b) := by
  apply finiteStoppedThreshold_measurable _ _ S hS b
  intro t
  exact (Measure.measurable_coe (hK.preimage measurable_subtype_coe)).comp (C.progressive t)

lemma cell_ball_live_of_radius
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hgrowth : PublishedDiskUnivalentGrowth)
    (t : ℝ≥0) (z : ℂ) (hz : z∈survivingDomain γ t) (r : ℝ) (hr : 0<r)
    (hR : fullRadius G t z=(2048*Real.pi)*r) :
    closedBall z (2*r) ⊆ survivingDomain γ t := by
  have hpos : 0<fullRadius G t z := by rw [hR]; positivity
  obtain ⟨_,hinner,_,hlive,_⟩ := hw.quarter_disk_chart_bounds hgrowth t z hz hpos
  have heq : fullRadius G t z/(1024*Real.pi)=2*r := by
    rw [hR]
    field_simp
    ring
  rw [heq] at hinner
  exact hinner.trans hlive

theorem CanonicalMass.finite_cell_mass_disk_tail
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
    (z : ℂ) (hz : z∈upperHalfPlane) (u v r b : ℝ)
    (hu : 0≤u) (hv : 0<v) (hr : 0<r)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (hlive : ∀ ω∈E, z∈survivingDomain (γ ω) (τ ω))
    (hbase : ∀ ω∈E, fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u))
    (hR : ∀ ω∈E, fullRadius (G ω) (τ ω) z=(2048*Real.pi)*r)
    (K : Set ℂ) (hK : MeasurableSet K) (hKball : K⊆closedBall z (2*r)) :
    ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
      finiteCenteredLaw P κ B γ G z (u+v)
        (A∩E∩C.finiteCellMassTest (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)) K
          (ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)) ≤
      ∫⁻ ω in A∩E, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
        (stoppedMarkedCenter κ B γ G τ z ω).arg
        ∂finiteCenteredLaw P κ B γ G z (u+v) := by
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
  have ha : ∀ ω, 0<a ω := stoppedMarkedScale_pos κ B γ G τ z
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
  intro A hA
  let T : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)
  let q := fun ω => R.angleDiskTail ν κ b v (θ ω)
  let test := C.finiteCellMassTest T K
    (ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)
  let S := E∩test
  let Z := fun ω => ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
    (γ ω) (G ω) z (u+v)/initialGreen κ z)
  let H : Set (Ω × C(ℝ≥0,ℝ)) := {x | x.1∈E ∧ b≤R.diskAtRadius κ (θ x.1) v x.2}
  let Dens : Ω × C(ℝ≥0,ℝ) → ℝ≥0∞ := fun x =>
    M x.1*canonicalFiniteDensity κ (v,Target.diskMapInv (θ x.1) 0,x.2)
  have hH : @MeasurableSet _ (hτ.measurableSpace.prod (borel _)) H :=
    (hE.preimage measurable_fst).inter (measurableSet_le measurable_const
      (@RawCanonicalMass.diskAtRadius_measurable (Ω × C(ℝ≥0,ℝ))
        (hτ.measurableSpace.prod (borel _)) R κ _ _ (hθm.comp measurable_fst)
        measurable_const Prod.snd measurable_snd))
  have hzm : Measurable[hτ.measurableSpace] (fun ω => Target.diskMapInv (θ ω) 0) := by
    unfold Target.diskMapInv
    fun_prop
  have hDens : @Measurable _ _ (hτ.measurableSpace.prod (borel _)) _ Dens :=
    (hM.comp measurable_fst).mul ((canonicalFiniteDensity_measurable κ).comp
      (measurable_const.prodMk ((hzm.comp measurable_fst).prodMk measurable_snd)))
  have hT := actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz
    (u+v) (by linarith)
  have htest : MeasurableSet test := hT.measurableSpace_le _
    (C.finiteCellMassTest_measurable T hT K hK _)
  have hS : MeasurableSet S := (hτ.measurableSpace_le _ hE).inter htest
  have hsec (ω : Ω) : (∫⁻ p, H.indicator Dens (ω,p) ∂ν)=
      E.indicator (fun ω => M ω*q ω) ω := by
    by_cases hω : ω∈E
    · let V := {p | b≤R.diskAtRadius κ (θ ω) v p}
      have hV : MeasurableSet V := measurableSet_le measurable_const
        (R.diskAtRadius_measurable κ (fun _ => θ ω) (fun _ => v)
          measurable_const measurable_const id measurable_id)
      have hid : (fun p => H.indicator Dens (ω,p)) =
          (fun p => M ω*V.indicator (fun p => canonicalFiniteDensity κ
            (v,Target.diskMapInv (θ ω) 0,p)) p) := by
        funext p
        by_cases hp : p∈V
        · rw [indicator_of_mem (show (ω,p)∈H from ⟨hω,hp⟩),indicator_of_mem hp]
        · rw [indicator_of_notMem (show (ω,p)∉H from fun h => hp h.2),
            indicator_of_notMem hp,mul_zero]
      rw [hid,lintegral_const_mul' _ _ (hMf ω),lintegral_indicator hV,
        ← withDensity_apply _ hV,indicator_of_mem hω]
      rfl
    · have hn (p : C(ℝ≥0,ℝ)) : (ω,p)∉H := fun h => hω h.1
      simp only [indicator_of_notMem hω]
      simp_rw [indicator_of_notMem (hn _)]
      exact lintegral_zero
  have hden := normalized_restart_disk_density hB hm hc γ G F hw hpublished τ hτ a ham ha
  have hcell := C.normalized_cell_bounds_at_radius hB hc hκ F hw R he D hD hDf hDp
    hgrowth hpublished τ hτ a ham ha
  have hactual : ∀ᵐ ω ∂P, S.indicator Z ω≤H.indicator Dens (ω,Y ω) := by
    filter_upwards [hden,hcell,hMactual] with ω hd hb hMω
    by_cases hSω : ω∈S
    · obtain ⟨hωE,ht⟩ := hSω
      have hpol := hpolar ω hωE
      have hmass := (hb (θ ω) hpol.1 z (hlive ω hωE) r hr (hR ω hωE)
        hpol.2 u hu (hbase ω hωE) v hv ht.1).2 K hK hKball (hKball.trans (cell_ball_live_of_radius (hw ω) hgrowth (τ ω) z (hlive ω hωE) r hr (hR ω hωE)))
      have heval : extendedCanonicalMass C.process C.rational.terminal (T ω) ω=
          C.process ((T ω).untopD 0) ω := by
        change (if T ω<⊤ then C.process ((T ω).untopD 0) ω else C.rational.terminal ω)=_
        exact ite_eq_left ht.1
      rw [heval] at hmass
      have hfpos : 0<ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ) := by
        apply ENNReal.ofReal_pos.mpr
        exact Real.rpow_pos_of_pos (by positivity) _
      have hval : b≤R.diskAtRadius κ (θ ω) v (Y ω) :=
        (ENNReal.ofReal_le_ofReal_iff (R.diskAtRadius_nonneg _ _ _ _)).mp
          ((ENNReal.mul_le_mul_iff_right hfpos.ne' ENNReal.ofReal_ne_top).mp (ht.2.trans hmass))
      have hDZ : Dens (ω,Y ω)=Z ω := by
        change M ω*canonicalFiniteDensity κ (v,Target.diskMapInv (θ ω) 0,Y ω)=Z ω
        rw [hMω hωE]
        exact (hd _ hpol.1 z (hlive ω hωE) hz hpol.2 u v hu hv (hbase ω hωE)).symm
      rw [indicator_of_mem (show (ω,Y ω)∈H from ⟨hωE,hval⟩),indicator_of_mem (show ω∈S from ⟨hωE,ht⟩),hDZ]
    · rw [indicator_of_notMem hSω]
      exact bot_le
  calc
    _ = ∫⁻ ω in A, S.indicator Z ω ∂P := by
      rw [setLIntegral_indicator hS,inter_comm S A,← inter_assoc]
      exact withDensity_apply _
        (((hτ.measurableSpace_le _ hA).inter (hτ.measurableSpace_le _ hE)).inter htest)
    _ ≤ ∫⁻ ω in A, H.indicator Dens (ω,Y ω) ∂P :=
      lintegral_mono_ae (ae_restrict_of_ae hactual)
    _ = ∫⁻ ω in A, ∫⁻ p, H.indicator Dens (ω,p) ∂ν ∂P :=
      restart_setLIntegral_random_test P ν hτ.measurableSpace hτ.measurableSpace_le
        Y hY hYlaw (H.indicator Dens) (hDens.indicator hH) A hA
    _ = ∫⁻ ω in A∩E, M ω*q ω ∂P := by
      simp_rw [hsec]
      rw [setLIntegral_indicator (hτ.measurableSpace_le _ hE),inter_comm E A]
    _ = _ := past_density_test_integral P _ hτ.measurableSpace hτ.measurableSpace_le
      M hM E hE hMpast q ((R.angleDiskTail_measurable ν κ b v).comp hθm) A hA

end SLEExactGauge.Multipoint

end

end OAI

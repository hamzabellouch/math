import OAI.Probability.SLE.Angle.CanonicalAngleKernel
import OAI.Probability.SLE.Geometry.ActualMarkedCell
import OAI.Probability.SLE.Geometry.PastDensityIntegral
import OAI.Probability.SLE.Geometry.FiniteDensityAtRadiusState
import OAI.Probability.SLE.Geometry.RestartWeightedKernel

namespace OAI

/-! Actual finite-centered angle transitions at a finite stopped radius
state. This identifies the transition before applying any mixing bound. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance centeredAngleMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance centeredAngleBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem finite_centered_angle_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t =>
      (hBm.of_uncurry_left : Measurable (B t)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (z : ℂ) (hz : z∈upperHalfPlane) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (hlive : ∀ ω∈E, z∈survivingDomain (γ ω) (τ ω))
    (hbase : ∀ ω∈E, fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u))
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫⁻ ω in A∩E, canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f
      (stoppedMarkedCenter κ B γ G τ z ω).arg ∂finiteCenteredLaw P κ B γ G z (u+v)) =
    ∫⁻ ω in A∩E, f (extendedMarkedAngle κ B γ G
      (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)) z ω)
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
  have hYlaw (D : Set Ω) (hD : MeasurableSet[hτ.measurableSpace] D) :
      (P.restrict D).map Y=P D • ν :=
    source_restart_random_scale_driver_law B hB hm hc τ hτ
      (fun ω => (a ω)⁻¹) ham.inv (fun ω => inv_pos.mpr (ha ω)) D hD
  have hYlaw0 : P.map Y=ν := by
    simpa only [Measure.restrict_univ,measure_univ,one_smul] using hYlaw univ MeasurableSet.univ
  obtain ⟨Φ,Gc,Fc,_hΦ,hW⟩ := exists_measurable_canonical_witness _ κ hpublished
  have hYw := canonical_witness_pullback hW Y hY hYlaw0
  have hpolar (ω : Ω) (hω : ω∈E) :
      θ ω∈Ioo (0:ℝ) Real.pi ∧ G ω (τ ω) z=
        (Real.sqrt κ*B (τ ω) ω:ℝ)+(a ω:ℂ)*Complex.exp (θ ω*Complex.I) := by
    have hh := (hw ω).live_marked_polar (τ ω) z (hlive ω hω)
    simpa only [θ,a,stoppedMarkedCenter_eq κ B γ G τ z ω (hlive ω hω),
      stoppedMarkedScale_eq_on_live B κ γ G F hw τ z ω (hlive ω hω)] using hh.2
  obtain ⟨M,hM,hMf,hMactual,hMpast⟩ := exists_finiteDensity_at_radius_state
    hB hBm hc h0 κ hκ hκ8 γ G F hw τ hτ z hz u v hu hv E hE hlive hbase
  let q := fun ω => canonicalAngleAverage ν κ v f (θ ω)
  have hq : Measurable[hτ.measurableSpace] q :=
    (canonicalAngleAverage_measurable ν κ v f hf).comp hθm
  let K : Ω × C(ℝ≥0,ℝ) → ℝ≥0∞ := fun x =>
    M x.1*canonicalFiniteDensity κ (v,Target.diskMapInv (θ x.1) 0,x.2)*
      f (canonicalStoppedAngle κ (v,Target.diskMapInv (θ x.1) 0,x.2))
  have hzM : Measurable[hτ.measurableSpace] (fun ω => Target.diskMapInv (θ ω) 0) := by
    unfold Target.diskMapInv
    fun_prop
  have hpM : @Measurable (Ω × C(ℝ≥0,ℝ)) _ (hτ.measurableSpace.prod (borel _)) _
      (fun x => (v,Target.diskMapInv (θ x.1) 0,x.2)) :=
    measurable_const.prodMk ((hzM.comp measurable_fst).prodMk measurable_snd)
  have hK : @Measurable _ _ (hτ.measurableSpace.prod (borel _)) _ K :=
    ((hM.comp measurable_fst).mul ((canonicalFiniteDensity_measurable κ).comp hpM)).mul
      (hf.comp ((canonicalStoppedAngle_measurable κ).comp hpM))
  have hsec (ω : Ω) : (∫⁻ p, K (ω,p) ∂ν)=M ω*q ω := by
    simp only [K,mul_assoc]
    rw [lintegral_const_mul' _ _ (hMf ω)]
    congr 1
    symm
    exact lintegral_withDensity_eq_lintegral_mul _
      ((canonicalFiniteDensity_measurable κ).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      (hf.comp ((canonicalStoppedAngle_measurable κ).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))))
  let Z : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (stoppedGreen κ
    (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) z (u+v)/initialGreen κ z)
  let g := fun ω => f (extendedMarkedAngle κ B γ G
    (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)) z ω)
  have hT := actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz
    (u+v) (by linarith)
  have hg : Measurable g := (hf.comp (extendedMarkedAngle_measurable B hm hc κ γ G F hw
    _ hT z)).mono hT.measurableSpace_le le_rfl
  have hZ : Measurable Z := by
    convert (canonicalFiniteDensity_measurable κ).comp
      (measurable_const.prodMk (measurable_const.prodMk (source_path_measurable (sourceDriverPath B hc) hm))) using 1
    funext ω
    exact (canonicalFiniteDensity_eq κ (sourceDriverPath B hc ω) (hw ω) (u+v)
      (by linarith) z).symm
  have hactual : ∀ᵐ ω ∂P, ω∈E → K (ω,Y ω)=Z ω*g ω := by
    filter_upwards [hYw,hMactual] with ω hwY hMω hωE
    have hp := hpolar ω hωE
    change M ω*canonicalFiniteDensity κ (v,Target.diskMapInv (θ ω) 0,Y ω)*
      f (canonicalStoppedAngle κ (v,Target.diskMapInv (θ ω) 0,Y ω))=Z ω*g ω
    rw [hMω hωE]
    have hn := (hw ω).normalized_disk_angle_test ((hc ω).const_mul _) κ (τ ω) (a ω)
      (ha ω) (Y ω) hwY (normalizedRestartDriverPath_driver κ B hc τ a ω)
      (θ ω) hp.1 z (hlive ω hωE) hz hp.2 u v hu hv (hbase ω hωE) f
    rw [hn]
    by_cases ht : radiusLevelTime (γ ω) (G ω) z (u+v)<∞
    · rw [show g ω=f ((G ω (radiusLevelTime (γ ω) (G ω) z (u+v)).toNNReal z-
          ((Real.sqrt κ*B (radiusLevelTime (γ ω) (G ω) z (u+v)).toNNReal ω:ℝ):ℂ)).arg) from
        congrArg f (extendedMarkedAngle_at_finite_radius κ B hc γ G F hw z (u+v) ω ht)]
    · simp only [Z,stoppedGreen,ite_eq_right ht,zero_div,ENNReal.ofReal_zero,zero_mul]
  have hAm : MeasurableSet (A∩E) := hτ.measurableSpace_le _ (hA.inter hE)
  calc
    (∫⁻ ω in A∩E, q ω ∂finiteCenteredLaw P κ B γ G z (u+v)) =
        ∫⁻ ω in A∩E, M ω*q ω ∂P :=
      (past_density_test_integral P _ hτ.measurableSpace hτ.measurableSpace_le M hM
        E hE hMpast q hq A hA).symm
    _ = ∫⁻ ω in A∩E, ∫⁻ p, K (ω,p) ∂ν ∂P := by simp only [hsec]
    _ = ∫⁻ ω in A∩E, K (ω,Y ω) ∂P :=
      (restart_setLIntegral_random_test P ν hτ.measurableSpace hτ.measurableSpace_le
        Y hY hYlaw K hK (A∩E) (hA.inter hE)).symm
    _ = ∫⁻ ω in A∩E, Z ω*g ω ∂P := by
      apply setLIntegral_congr_fun_ae hAm
      filter_upwards [hactual] with ω hω hωAE
      exact hω hωAE.2
    _ = ∫⁻ ω in A∩E, g ω ∂P.withDensity Z :=
      (setLIntegral_withDensity_eq_setLIntegral_mul _ hZ hg hAm).symm

end SLEExactGauge

end

end OAI

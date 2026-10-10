import OAI.Probability.SLE.Geometry.FiniteCenteredAngleKernel
import OAI.Probability.SLE.Gauge.PrescribedRadiusFinalLaw

namespace OAI

/-! The finite-centered angle transition on the full past of a literal
radius time, and under every later finite centered law. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance radiusAngleMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance radiusAngleBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem radius_angle_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (z : ℂ) (hz : z∈upperHalfPlane) (u v V : ℝ) (hu : 0 ≤ u) (hv : 0 < v)
    (hV : u+v ≤ V) (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (A : Set Ω) (hA : MeasurableSet[(actual_radiusLevelTime_stopping hB
      (fun t => (hBm.of_uncurry_left : Measurable (B t))) hBm hc h0
      κ hκ hκ8 γ G F hw z hz u hu).measurableSpace] A) :
    (∫⁻ ω in A, canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f
      (extendedMarkedAngle κ B γ G (fun ω => radiusLevelTime (γ ω) (G ω) z u) z ω)
      ∂finiteCenteredLaw P κ B γ G z V) =
    ∫⁻ ω in A, f (extendedMarkedAngle κ B γ G
      (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)) z ω)
      ∂finiteCenteredLaw P κ B γ G z V := by
  classical
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let σ : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  let T : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)
  have hσ : IsStoppingTime ℱ σ :=
    actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz u hu
  have hT : IsStoppingTime ℱ T :=
    actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz (u+v) (by linarith)
  let ν := P.map (sourceDriverPath B hc)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  let Q := finiteCenteredLaw P κ B γ G z (u+v)
  let QV := finiteCenteredLaw P κ B γ G z V
  let L := fun ω => canonicalAngleAverage ν κ v f (extendedMarkedAngle κ B γ G σ z ω)
  let R := fun ω => f (extendedMarkedAngle κ B γ G T z ω)
  let E := fun n : ℕ => A∩{ω | σ ω≤((n:ℝ≥0):WithTop ℝ≥0)}
  have hEm (n : ℕ) : MeasurableSet (E n) :=
    hσ.measurableSpace_le _ (hA.inter (hσ.measurableSet_le' n))
  have hmono : Monotone E := by
    intro n k hnk ω hω
    change ω∈A ∧ σ ω≤((n:ℝ≥0):WithTop ℝ≥0) at hω
    change ω∈A ∧ σ ω≤((k:ℝ≥0):WithTop ℝ≥0)
    exact ⟨hω.1,hω.2.trans (WithTop.coe_le_coe.mpr (by exact_mod_cast hnk))⟩
  have hfinite : ∀ᵐ ω ∂Q, σ ω≠⊤ :=
    finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F (Eventually.of_forall hw)
      z hz u (u+v) hu (by linarith) σ (Eventually.of_forall fun _ => le_rfl)
  have hcover := stopped_past_cover_of_ae_finite Q σ hfinite A
  have hlocal (n : ℕ) : (∫⁻ ω in E n, L ω ∂Q)=(∫⁻ ω in E n, R ω ∂Q) := by
    let τ := cutoffStop σ n
    have hτ := cutoffStop_stopping ℱ σ hσ (n:ℝ≥0)
    have hEn := cutoffStop_success_measurable ℱ σ hσ n A hA
    have hstate (ω : Ω) (hω : ω∈E n) :
        z∈survivingDomain (γ ω) (τ ω) ∧
        fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u) := by
      rw [show τ ω=(σ ω).untopD 0 from cutoffStop_eq_on_success σ n ω hω.2]
      exact actual_radius_level_finite_state (hw ω) ((hc ω).const_mul _) z u
        (ne_top_of_le_ne_top WithTop.coe_ne_top hω.2)
    have hh := finite_centered_angle_kernel hB hBm hc h0 hκ hκ8 γ G F hw hpublished
      τ hτ z hz u v hu hv (E n) hEn (fun ω hω => (hstate ω hω).1)
      (fun ω hω => (hstate ω hω).2) f hf univ MeasurableSet.univ
    simp only [univ_inter] at hh
    have hid (ω : Ω) (hω : ω∈E n) : L ω=
        canonicalAngleAverage ν κ v f (stoppedMarkedCenter κ B γ G τ z ω).arg := by
      dsimp only [L,extendedMarkedAngle]
      rw [ite_eq_right (ne_top_of_le_ne_top WithTop.coe_ne_top hω.2)]
      congr 2
      exact (stoppedMarkedCenter_time_congr κ B γ G τ
        (fun ω => (σ ω).untopD 0) z ω (cutoffStop_eq_on_success σ n ω hω.2)).symm
    rw [setLIntegral_congr_fun (hEm n) hid]
    exact hh
  have hexhaust (g : Ω → ℝ≥0∞) : (∫⁻ ω in A, g ω ∂Q)=⨆ n, ∫⁻ ω in E n, g ω ∂Q := by
    have habs : (Q.withDensity g).AbsolutelyContinuous Q := withDensity_absolutelyContinuous Q g
    calc
      _ = Q.withDensity g A := (withDensity_apply _ (hσ.measurableSpace_le _ hA)).symm
      _ = Q.withDensity g (⋃ n, E n) := measure_congr (habs.ae_le hcover)
      _ = ⨆ n, Q.withDensity g (E n) := hmono.measure_iUnion
      _ = _ := by congr 1; funext n; exact withDensity_apply _ (hEm n)
  have hbase : (∫⁻ ω in A, L ω ∂Q)=(∫⁻ ω in A, R ω ∂Q) := by
    rw [hexhaust L,hexhaust R]
    exact iSup_congr hlocal
  have hσT (ω : Ω) : σ ω≤T ω :=
    radiusLevelTime_mono ((hc ω).const_mul _) (hw ω) z hu (by linarith)
  have hLT : Measurable[hT.measurableSpace] L :=
    ((canonicalAngleAverage_measurable ν κ v f hf).comp
      (extendedMarkedAngle_measurable B hm hc κ γ G F hw σ hσ z)).mono
        (hσ.measurableSpace_mono hT hσT) le_rfl
  have hRT : Measurable[hT.measurableSpace] R :=
    hf.comp (extendedMarkedAngle_measurable B hm hc κ γ G F hw T hT z)
  have hAT : MeasurableSet[hT.measurableSpace] A := hσ.measurableSpace_mono hT hσT A hA
  have hcons (g : Ω → ℝ≥0∞) (hg : Measurable[hT.measurableSpace] g) :
      (∫⁻ ω in A, g ω ∂QV)=(∫⁻ ω in A, g ω ∂Q) := by
    have hh := @lintegral_eq_of_stopped_events Ω mΩ QV Q hT.measurableSpace
      hT.measurableSpace_le (fun D hD => finiteCenteredLaw_consistent_at_radius_stop
        hB hBm hc h0 κ hκ hκ8 γ G F (Eventually.of_forall hw) z hz (u+v) V
        (by linarith) hV T hT (Eventually.of_forall fun _ => rfl) D hD)
      (A.indicator g) (hg.indicator hAT)
    simpa only [lintegral_indicator (hT.measurableSpace_le _ hAT)] using hh
  change (∫⁻ ω in A, L ω ∂QV)=(∫⁻ ω in A, R ω ∂QV)
  rw [hcons L hLT,hcons R hRT]
  exact hbase

end SLEExactGauge

end

end OAI

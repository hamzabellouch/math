import OAI.Probability.SLE.Gauge.PrescribedDiskConditional
import OAI.Probability.SLE.Geometry.ExtendedDiskAngle

namespace OAI

/-! The prescribed disk success kernel at the literal radius stop. Finite
cutoffs exhaust that stop under the actual finite centered law. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance radiusTestMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance radiusTestBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.prescribed_disk_test_at_radius
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
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u v r b : ℝ)
    (hu : 0 ≤ u) (hv : 0 < v) (hr : 0 < r)
    (hR : (2*z.im)*Real.exp (-u)=(2048*Real.pi)*r) :
    ∀ A : Set Ω, MeasurableSet[(actual_radiusLevelTime_stopping hB
      (fun t => (hBm.of_uncurry_left : Measurable (B t))) hBm hc h0
      κ hκ hκ8 γ G F hw z hz u hu).measurableSpace] A →
      (∫⁻ ω in A, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
        (extendedMarkedAngle κ B γ G (fun ω => radiusLevelTime (γ ω) (G ω) z u) z ω)
        ∂finiteCenteredLaw P κ B γ G z (u+v)) ≤
      finiteCenteredLaw P κ B γ G z (u+v)
        (A∩C.prescribedBallTest (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v))
          z ((4096*Real.pi)*r)
          (ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)) := by
  classical
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let σ : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  have hσ : IsStoppingTime ℱ σ :=
    actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz u hu
  let Q := finiteCenteredLaw P κ B γ G z (u+v)
  let f := fun ω => R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
    (extendedMarkedAngle κ B γ G σ z ω)
  let test := C.prescribedBallTest (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v))
    z ((4096*Real.pi)*r) (ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)
  intro A hA
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
  have hbound (n : ℕ) : (∫⁻ ω in E n, f ω ∂Q) ≤ Q (A∩test) := by
    let τ := cutoffStop σ n
    have hτ := cutoffStop_stopping ℱ σ hσ (n:ℝ≥0)
    have hEn : MeasurableSet[hτ.measurableSpace] (E n) :=
      cutoffStop_success_measurable ℱ σ hσ n A hA
    have hstate (ω : Ω) (hω : ω∈E n) :
        z ∈ survivingDomain (γ ω) (τ ω) ∧
        fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u) := by
      rw [show τ ω=(σ ω).untopD 0 from cutoffStop_eq_on_success σ n ω hω.2]
      exact actual_radius_level_finite_state (hw ω) ((hc ω).const_mul _) z u
        (ne_top_of_le_ne_top WithTop.coe_ne_top hω.2)
    have hh := C.prescribed_disk_conditional_bound hB hc h0 hκ hκ8 F hw R he
      D hD hDf hDp hgrowth hpublished τ hτ z hz u v r b hu hv hr (E n) hEn
      (fun ω hω => (hstate ω hω).1) (fun ω hω => (hstate ω hω).2)
      (fun ω hω => (hstate ω hω).2.trans hR) univ MeasurableSet.univ
    simp only [univ_inter] at hh
    have hid (ω : Ω) (hω : ω∈E n) : f ω=R.angleDiskTail
        (P.map (sourceDriverPath B hc)) κ b v (stoppedMarkedCenter κ B γ G τ z ω).arg := by
      dsimp only [f,extendedMarkedAngle]
      rw [ite_eq_right (ne_top_of_le_ne_top WithTop.coe_ne_top hω.2)]
      congr 2
      exact (stoppedMarkedCenter_time_congr κ B γ G τ
        (fun ω => (σ ω).untopD 0) z ω (cutoffStop_eq_on_success σ n ω hω.2)).symm
    rw [setLIntegral_congr_fun (hEm n) hid]
    exact hh.trans (measure_mono (inter_subset_inter inter_subset_left subset_rfl))
  have hcover : A =ᵐ[Q] ⋃ n, E n := by
    filter_upwards [hfinite] with ω hω
    apply propext
    constructor
    · intro hAω
      lift σ ω to ℝ≥0 using hω with t ht
      obtain ⟨n,hn⟩ := exists_nat_ge (t:ℝ)
      exact mem_iUnion.mpr ⟨n,hAω,by
        change σ ω≤((n:ℝ≥0):WithTop ℝ≥0)
        rw [← ht]
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast hn)⟩
    · intro hωE
      obtain ⟨n,hn⟩ := mem_iUnion.mp hωE
      exact hn.1
  have habs : (Q.withDensity f).AbsolutelyContinuous Q := withDensity_absolutelyContinuous Q f
  calc
    (∫⁻ ω in A, f ω ∂Q) = Q.withDensity f A := (withDensity_apply _ (hσ.measurableSpace_le _ hA)).symm
    _ = Q.withDensity f (⋃ n, E n) := measure_congr (habs.ae_le hcover)
    _ = ⨆ n, Q.withDensity f (E n) := hmono.measure_iUnion
    _ ≤ Q (A∩test) := iSup_le fun n => by
      rw [withDensity_apply _ (hEm n)]
      exact hbound n

end SLEExactGauge.Multipoint

end

end OAI

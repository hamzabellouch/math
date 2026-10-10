import OAI.Probability.SLE.Geometry.FiniteCellTailKernel
import OAI.Probability.SLE.Geometry.ExtendedDiskAngle

namespace OAI

/-! The physical cell-tail bound at a literal, possibly infinite radius
start. Finite cutoffs exhaust the actual centered law. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance cellTailRadiusMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance cellTailRadiusBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.cell_mass_disk_tail_at_radius
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
    (z : ℂ) (hz : z∈upperHalfPlane) (u v r b : ℝ)
    (hu : 0≤u) (hv : 0<v) (hr : 0<r)
    (hR : (2*z.im)*Real.exp (-u)=(2048*Real.pi)*r)
    (K : Set ℂ) (hK : MeasurableSet K) (hKball : K⊆closedBall z (2*r)) :
    ∀ A : Set Ω, MeasurableSet[(actual_radiusLevelTime_stopping hB
      (fun t => (hBm.of_uncurry_left : Measurable (B t))) hBm hc h0
      κ hκ hκ8 γ G F hw z hz u hu).measurableSpace] A →
      finiteCenteredLaw P κ B γ G z (u+v)
        (A∩C.finiteCellMassTest (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)) K
          (ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)) ≤
      ∫⁻ ω in A, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
        (extendedMarkedAngle κ B γ G (fun ω => radiusLevelTime (γ ω) (G ω) z u) z ω)
        ∂finiteCenteredLaw P κ B γ G z (u+v) := by
  classical
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let σ : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  have hσ : IsStoppingTime ℱ σ :=
    actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz u hu
  let Q := finiteCenteredLaw P κ B γ G z (u+v)
  let f := fun ω => R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
    (extendedMarkedAngle κ B γ G σ z ω)
  let test := C.finiteCellMassTest (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)) K
    (ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)
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
  have hbound (n : ℕ) : Q (E n∩test) ≤ ∫⁻ ω in E n, f ω ∂Q := by
    let τ := cutoffStop σ n
    have hτ := cutoffStop_stopping ℱ σ hσ (n:ℝ≥0)
    have hEn := cutoffStop_success_measurable ℱ σ hσ n A hA
    have hstate (ω : Ω) (hω : ω∈E n) :
        z∈survivingDomain (γ ω) (τ ω) ∧
        fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u) := by
      rw [show τ ω=(σ ω).untopD 0 from cutoffStop_eq_on_success σ n ω hω.2]
      exact actual_radius_level_finite_state (hw ω) ((hc ω).const_mul _) z u
        (ne_top_of_le_ne_top WithTop.coe_ne_top hω.2)
    have hh := C.finite_cell_mass_disk_tail hB hc h0 hκ hκ8 F hw R he D hD hDf hDp
      hgrowth hpublished τ hτ z hz u v r b hu hv hr (E n) hEn
      (fun ω hω => (hstate ω hω).1) (fun ω hω => (hstate ω hω).2)
      (fun ω hω => (hstate ω hω).2.trans hR) K hK hKball univ MeasurableSet.univ
    simp only [univ_inter] at hh
    have hid (ω : Ω) (hω : ω∈E n) : f ω=R.angleDiskTail
        (P.map (sourceDriverPath B hc)) κ b v (stoppedMarkedCenter κ B γ G τ z ω).arg := by
      dsimp only [f,extendedMarkedAngle]
      rw [ite_eq_right (ne_top_of_le_ne_top WithTop.coe_ne_top hω.2)]
      congr 2
      exact (stoppedMarkedCenter_time_congr κ B γ G τ
        (fun ω => (σ ω).untopD 0) z ω (cutoffStop_eq_on_success σ n ω hω.2)).symm
    rw [setLIntegral_congr_fun (hEm n) hid]
    exact hh
  have hcover := stopped_past_cover_of_ae_finite Q σ hfinite A
  have hcover' : A∩test =ᵐ[Q] (⋃ n, E n)∩test := by
    filter_upwards [hcover] with ω hω
    exact propext (and_congr_left fun _ => Iff.of_eq hω)
  have hmono' : Monotone (fun n => E n∩test) := fun _ _ h => inter_subset_inter (hmono h) subset_rfl
  calc
    Q (A∩test)=Q ((⋃ n, E n)∩test) := measure_congr hcover'
    _ = Q (⋃ n, E n∩test) := by rw [iUnion_inter]
    _ = ⨆ n, Q (E n∩test) := hmono'.measure_iUnion
    _ ≤ ∫⁻ ω in A, f ω ∂Q := iSup_le fun n =>
      (hbound n).trans (lintegral_mono_set inter_subset_left)

end SLEExactGauge.Multipoint

end

end OAI

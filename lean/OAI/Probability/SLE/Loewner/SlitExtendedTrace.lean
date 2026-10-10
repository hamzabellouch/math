import OAI.Probability.SLE.Loewner.SlitConstantDriverTail
import OAI.Probability.SLE.Loewner.SlitBoundaryTip
import OAI.Probability.SLE.Loewner.RawConstantTailTrace
import OAI.Probability.SLE.Geometry.ConcatenatedSlitGeometry
import OAI.Probability.SLE.Loewner.SmoothRawGeometry

namespace OAI

/-! The exact finite slit followed by its vertical image is the raw trace
of the constructed, globally continuous driver. -/
noncomputable section
open Set Filter Function Complex _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

theorem slitCapacity_raw_trace_concat (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) (B : ℂ → ℂ)
    (hB : ∀ z∈upperHalfPlane, B z=initialInverseChart p hi h0 hH T z) :
    (fun t : ℝ≥0 => Target.trace 1 (slitCapacityDriver p hi h0 hH hT) t)=
      concatenateSlit (slitCapacityHorizon p hi h0 hH T)
        (slitCapacityCurve p hi h0 hH T) (fun t => Target.trace 1 (Target.linearDriver 0) t)
        B (initialDrivingValue p hi h0 hH T hT) := by
  funext t
  let A := slitCapacityHorizon p hi h0 hH T
  let u := initialDrivingValue p hi h0 hH T hT
  change Target.trace 1 (slitCapacityDriver p hi h0 hH hT) t=
    concatenateSlit A (slitCapacityCurve p hi h0 hH T)
      (fun s => Target.trace 1 (Target.linearDriver 0) s) B u t
  by_cases ht : t ≤ A
  · exact (slitCapacity_raw_trace_eq p hi h0 hH hT ht).trans (by
      simp only [concatenateSlit,ite_eq_left ht])
  · have hAt : A<t := lt_of_not_ge ht
    have hS : 0<t-A := tsub_pos_iff_lt.mpr hAt
    have hη := Target.smooth_raw_trace_mem_upperHalfPlane (Target.linearDriver 0) (t-A) hS
      (fun _ => 0) (fun s hs => (Target.linearDriver_derivative 0 s hs.1).mono Icc_subset_Ici_self)
      (show (0:ℝ) ≤ 0 from le_rfl) (fun _ _ => by simp)
    have hw : (u:ℂ)+Target.trace 1 (Target.linearDriver 0) (t-A : ℝ≥0)∈upperHalfPlane := by
      simpa only [upperHalfPlane,mem_ofPred_eq,add_im,ofReal_im,zero_add] using hη
    have he := Target.trace_constant_tail (slitCapacityDriver p hi h0 hH hT) A (t-A) hS u
      (fun s hs => slitCapacityDriver_after p hi h0 hH hT hs)
    rw [←NNReal.coe_add,add_tsub_cancel_of_le hAt.le] at he
    rw [he,concatenateSlit,ite_eq_right ht,hB _ hw]
    rw [slitCapacityInverse_eq_raw p hi h0 hH hT le_rfl hw]
    change initialInverseChart p hi h0 hH (slitCapacityTime p hi h0 hH T A) _=_
    rw [slitCapacityTime_after p hi h0 hH T le_rfl]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}

theorem RegularSLEPresentation.slitCapacity_raw_geometry
    (a : RegularSLEPresentation P κ γ) (hκ : 0<κ)
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT0 : 0<T) (hT : T<1) :
    let β := fun t : ℝ≥0 => Target.trace 1 (slitCapacityDriver p hi h0 hH hT) t
    Continuous β ∧ β 0=0 ∧ Injective β ∧ (∀ t, 0<t → β t∈upperHalfPlane) ∧
      ∀ t, 0<t → upperHalfPlane \ (β '' Icc 0 t) ⊆ survivingDomain β t := by
  dsimp only
  let A := slitCapacityHorizon p hi h0 hH T
  let u := initialDrivingValue p hi h0 hH T hT
  let η := fun t : ℝ≥0 => Target.trace 1 (Target.linearDriver 0) t
  let β := slitCapacityCurve p hi h0 hH T
  have hd : ∀ t, 0 ≤ t → HasDerivWithinAt (Target.driverValue (Target.linearDriver 0)) 0
      (Ici 0) t := fun t ht => Target.linearDriver_derivative 0 t ht
  have hb : ∀ t : ℝ, 0 ≤ t → |(0:ℝ)| ≤ (0:ℝ≥0) := by intros; simp
  have hηc : Continuous η := Target.continuous_smooth_raw_trace _ (fun _ => 0) 0 hd hb
  have hη0 : η 0=0 := Target.smooth_trace_zero _ (fun _ => 0) 0 hd hb
  have hηi : Injective η := a.smooth_raw_trace_injective hκ _ (fun _ => 0) 0 hd hb
  have hηH (t : ℝ≥0) (ht : 0<t) : η t∈upperHalfPlane :=
    Target.smooth_raw_trace_mem_upperHalfPlane _ t ht (fun _ => 0)
      (fun s hs => (hd s hs.1).mono Icc_subset_Ici_self) (show (0:ℝ) ≤ 0 from le_rfl)
      (fun _ _ => by simp)
  have hηclosed (t : ℝ≥0) : 0 ≤ (η t).im := by
    by_cases ht : t=0
    · simp only [ht,hη0,zero_im,le_refl]
    · exact (show 0<(η t).im from hηH t (pos_iff_ne_zero.mpr ht)).le
  obtain ⟨B,hBc,hBF,hBu⟩ := exists_initial_inverse_boundary_tip p hi h0 hH hT
  have hBc' : ContinuousOn B closedHalfPlane := hBc
  have hβc : Continuous β := slitCapacityCurve_continuous p hi h0 hH T
  have hβ0 : β 0=0 := slitCapacityCurve_zero p hi h0 hH T
  have hβi : InjOn β (Icc 0 A) := slitCapacityCurve_injOn p hi h0 hH T
  have hβH (t : ℝ≥0) (ht : 0<t) : β t∈upperHalfPlane := by
    by_cases htA : t ≤ A
    · exact slitCapacityCurve_positive p hi h0 hH T ⟨ht,htA⟩
    · change p (slitCapacityTime p hi h0 hH T t)∈upperHalfPlane
      rw [slitCapacityTime_after p hi h0 hH T (le_of_not_ge htA)]
      exact hH T (ne_of_gt hT0)
  have hBA : B (u:ℂ)=β A := by
    change B (u:ℂ)=p (slitCapacityTime p hi h0 hH T A)
    rw [slitCapacityTime_after p hi h0 hH T le_rfl]
    exact hBu
  have hA : 0<A := div_pos (initialCapacity_pos p hi h0 hH (ne_of_gt hT0)) (by norm_num)
  have hBi : InjOn B upperHalfPlane := by
    intro z hz w hw he
    apply initialInverseChart_injOn p hi h0 hH T hz hw
    simpa only [hBF z hz,hBF w hw] using he
  have hBmap : MapsTo B upperHalfPlane (survivingDomain β A) := by
    intro z hz
    apply slitCapacityCurve_free_complement p hi h0 hH T le_rfl hA
    rw [slitCapacityCurve_initial_range p hi h0 hH T le_rfl,
      slitCapacityTime_after p hi h0 hH T le_rfl,hBF z hz]
    exact initialInverseChart_mem_domain p hi h0 hH T hz
  let f := concatenateSlit A β η B u
  have hf : (fun t : ℝ≥0 => Target.trace 1 (slitCapacityDriver p hi h0 hH hT) t)=f :=
    slitCapacity_raw_trace_concat p hi h0 hH hT B hBF
  have hg : Continuous f ∧ f 0=0 ∧ Injective f ∧ (∀ t, 0<t → f t∈upperHalfPlane) ∧
      ∀ t, 0<t → upperHalfPlane \ (f '' Icc 0 t) ⊆ survivingDomain f t :=
    ⟨continuous_concatenateSlit A β η B u hβc hηc hη0 hηclosed hBc' hBA,
    by simp only [f,concatenateSlit,ite_eq_left (show (0:ℝ≥0) ≤ A from zero_le),hβ0],
    concatenateSlit_injective A β η B u hβi hηi hηH hBi hBmap,
    concatenateSlit_positive A β η B u hβH hηH (fun _ hz => (hBmap hz).1.1),
    concatenateSlit_free_complement A β η B u hβc hηc hβ0 hη0 hβi hηi hβH hηH
      hBc' hBA hBi hBmap⟩
  simpa only [←hf] using hg

end SLEExactGauge

end

end OAI

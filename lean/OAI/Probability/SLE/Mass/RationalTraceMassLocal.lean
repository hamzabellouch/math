import OAI.Probability.SLE.Mass.RationalTraceMassVariation
import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! Rational-time reconstruction on the open half-plane. The terminal
measure is only locally finite; the trace is allowed to touch the real
line. Compact test supports supply the finite ambient control measures. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology ENNReal CompactlySupported

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

structure HalfPlaneTraceIncrements (μ : ℚ → Measure upperHalfPlane)
    (ν : Measure upperHalfPlane) (γ : ℝ → ℂ) : Prop where
  regular : ∀ q, (μ q).Regular
  dominated : ∀ q, μ q ≤ ν
  increment : ∀ p q, p ≤ q → ∃ η : Measure upperHalfPlane,
    μ q = μ p + η ∧ η ≤ ν.restrict {z : upperHalfPlane | (z : ℂ) ∈ γ '' Icc (p:ℝ) q}

lemma HalfPlaneTraceIncrements.monotone
    {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane} {γ : ℝ → ℂ}
    (H : HalfPlaneTraceIncrements μ ν γ) : Monotone μ := by
  intro p q hpq
  obtain ⟨η,hη,_⟩ := H.increment p q hpq
  rw [hη]
  exact Measure.le_add_right le_rfl

def ambientCompactRestriction (ν : Measure upperHalfPlane) (K : Set upperHalfPlane) : Measure ℂ :=
  Measure.map (Subtype.val : upperHalfPlane → ℂ) (ν.restrict K)

lemma ambientCompactRestriction_finite (ν : Measure upperHalfPlane)
    [IsFiniteMeasureOnCompacts ν] (K : Set upperHalfPlane) (hK : IsCompact K) :
    IsFiniteMeasure (ambientCompactRestriction ν K) := by
  have : Fact (ν K < ⊤) := ⟨hK.measure_lt_top⟩
  exact inferInstanceAs (IsFiniteMeasure ((ν.restrict K).map (Subtype.val : upperHalfPlane → ℂ)))

lemma ambientCompactRestriction_nullSingletons (ν : Measure upperHalfPlane)
    [NullSingletonClass ν] (K : Set upperHalfPlane) :
    NullSingletonClass (ambientCompactRestriction ν K) := by
  constructor
  intro z
  rw [ambientCompactRestriction,Measure.map_apply measurable_subtype_coe (measurableSet_singleton z)]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply Subtype.ext
  exact (mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm

lemma HalfPlaneTraceIncrements.integral_dist_le
    {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane} [ν.Regular]
    {γ : ℝ → ℂ} (H : HalfPlaneTraceIncrements μ ν γ) (hγ : Continuous γ)
    (f : C_c(upperHalfPlane,ℝ)) (p q : ℚ) :
    dist (∫ z, f z ∂μ p) (∫ z, f z ∂μ q) ≤ ‖f.toBoundedContinuousFunction‖ *
      (ambientCompactRestriction ν (tsupport f)
        (γ '' Icc (min (p:ℝ) q) (max (p:ℝ) q))).toReal := by
  have ordered (a b : ℚ) (hab : a ≤ b) :
      dist (∫ z, f z ∂μ a) (∫ z, f z ∂μ b) ≤ ‖f.toBoundedContinuousFunction‖ *
        (ambientCompactRestriction ν (tsupport f) (γ '' Icc (a:ℝ) b)).toReal := by
    let K := tsupport f
    let A : Set upperHalfPlane := {z | (z : ℂ) ∈ γ '' Icc (a:ℝ) b}
    have hAm : MeasurableSet A :=
      (isCompact_Icc.image hγ).measurableSet.preimage measurable_subtype_coe
    obtain ⟨η,hη,hην⟩ := H.increment a b hab
    have hηle : η ≤ ν := hην.trans Measure.restrict_le_self
    let : IsFiniteMeasureOnCompacts η := ⟨fun L hL => (hηle L).trans_lt hL.measure_lt_top⟩
    let : (μ a).Regular := H.regular a
    have hηK : η K < ⊤ := f.hasCompactSupport.measure_lt_top
    have : Fact (η K < ⊤) := ⟨hηK⟩
    let : IsFiniteMeasure (η.restrict K) := inferInstance
    let : IsFiniteMeasure (ambientCompactRestriction ν K) :=
      ambientCompactRestriction_finite ν K f.hasCompactSupport
    have hbound : η K ≤ ambientCompactRestriction ν K (γ '' Icc (a:ℝ) b) := by
      calc
        η K ≤ ν.restrict A K := hην K
        _ = ν (K ∩ A) := Measure.restrict_apply f.hasCompactSupport.measurableSet
        _ = ambientCompactRestriction ν K (γ '' Icc (a:ℝ) b) := by
          rw [ambientCompactRestriction,Measure.map_apply measurable_subtype_coe
            (isCompact_Icc.image hγ).measurableSet]
          change ν (K ∩ A) = ν.restrict K A
          rw [Measure.restrict_apply hAm,inter_comm]
    rw [hη,integral_add_measure f.integrable f.integrable,dist_eq_norm]
    have hsub : (∫ z, f z ∂μ a)-((∫ z, f z ∂μ a)+(∫ z, f z ∂η)) = -(∫ z, f z ∂η) := by ring
    rw [hsub,norm_neg,← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)]
    have hb := norm_integral_le_of_norm_le_const (μ := η.restrict K)
      (ae_of_all _ (fun z => f.toBoundedContinuousFunction.norm_coe_le_norm z))
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply ENNReal.toReal_mono (measure_ne_top (ambientCompactRestriction ν K) _)
    simpa only [Measure.restrict_apply_univ] using hbound
  rcases le_total p q with h | h
  · simpa only [min_eq_left (Rat.cast_le.mpr h),max_eq_right (Rat.cast_le.mpr h)] using ordered p q h
  · rw [dist_comm]
    simpa only [min_eq_right (Rat.cast_le.mpr h),max_eq_left (Rat.cast_le.mpr h)] using ordered q p h

lemma HalfPlaneTraceIncrements.continuous_test_extension
    {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane} [ν.Regular]
    [NullSingletonClass ν] {γ : ℝ → ℂ}
    (H : HalfPlaneTraceIncrements μ ν γ) (hγ : Continuous γ) (f : C_c(upperHalfPlane,ℝ)) :
    ∃ F : ℝ → ℝ, Continuous F ∧ (∀ q : ℚ, F q = ∫ z, f z ∂μ q) ∧
      ∀ G : ℝ → ℝ, Continuous G → (∀ q : ℚ, G q = ∫ z, f z ∂μ q) → G = F := by
  let ρ := ambientCompactRestriction ν (tsupport f)
  let : IsFiniteMeasure ρ := ambientCompactRestriction_finite ν _ f.hasCompactSupport
  let : NullSingletonClass ρ := ambientCompactRestriction_nullSingletons ν _
  exact continuous_rational_extension_of_trace_control ρ γ hγ
    (fun q => ∫ z, f z ∂μ q) ‖f.toBoundedContinuousFunction‖ (norm_nonneg _)
    (H.integral_dist_le hγ f)

/-- One locally finite Radon family extends all rational times. Every
compact test is continuous, even when the physical trace meets the real line. -/
theorem HalfPlaneTraceIncrements.exists_continuous_extension
    {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane} [ν.Regular]
    [NullSingletonClass ν] {γ : ℝ → ℂ}
    (H : HalfPlaneTraceIncrements μ ν γ) (hγ : Continuous γ) :
    ∃ M : ℝ → Measure upperHalfPlane, (∀ t, (M t).Regular) ∧ (∀ t, M t ≤ ν) ∧
      (∀ q : ℚ, M q = μ q) ∧
      (∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂M t)) ∧ Monotone M := by
  choose F hFc hFq _ using H.continuous_test_extension hγ
  have hex (t : ℝ) : ∃ η : Measure upperHalfPlane, η.Regular ∧ IsFiniteMeasureOnCompacts η ∧
      ∀ f : C_c(upperHalfPlane,ℝ), (∫ z, f z ∂η) = F f t := by
    obtain ⟨q,hq⟩ := exists_rational_sequence_tendsto t
    let (n : ℕ) : (μ (q n)).Regular := H.regular (q n)
    have hlim (f : C_c(upperHalfPlane,ℝ)) :
        Tendsto (fun n => ∫ z, f z ∂μ (q n)) atTop (𝓝 (F f t)) := by
      simpa only [Function.comp_def,hFq] using (hFc f).continuousAt.tendsto.comp hq
    obtain ⟨η,hηr,hηf,hηlim⟩ := radon_limit_of_all_test_limits (fun n => μ (q n))
      (fun f => ⟨F f t,hlim f⟩)
    exact ⟨η,hηr,hηf,fun f => tendsto_nhds_unique (hηlim f) (hlim f)⟩
  choose M hMr hMf hMI using hex
  have hcont (f : C_c(upperHalfPlane,ℝ)) : Continuous (fun t => ∫ z, f z ∂M t) := by
    simpa only [hMI] using hFc f
  have hrat (q : ℚ) : M q = μ q := by
    let : (M q).Regular := hMr q
    let : (μ q).Regular := H.regular q
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [hMI,hFq]
  have hdom (t : ℝ) : M t ≤ ν := by
    let : (M t).Regular := hMr t
    obtain ⟨q,hq⟩ := exists_rational_sequence_tendsto t
    apply radon_measure_le_of_nonneg_tests
    intro f hfn
    have hlim : Tendsto (fun n => ∫ z, f z ∂μ (q n)) atTop (𝓝 (∫ z, f z ∂M t)) := by
      simpa only [Function.comp_def,hrat] using (hcont f).continuousAt.tendsto.comp hq
    apply le_of_tendsto_of_tendsto' hlim tendsto_const_nhds
    intro n
    exact integral_mono_measure (H.dominated (q n)) (ae_of_all ν hfn) f.integrable
  refine ⟨M,hMr,hdom,hrat,hcont,?_⟩
  intro s t hst
  rcases eq_or_lt_of_le hst with rfl | hst
  · exact le_rfl
  let : (M s).Regular := hMr s
  let : (M t).Regular := hMr t
  obtain ⟨p,hp⟩ := exists_rational_sequence_tendsto s
  obtain ⟨q,hq⟩ := exists_rational_sequence_tendsto t
  have hp' : ∀ᶠ n in atTop, (p n : ℝ) < (s+t)/2 := hp.eventually (gt_mem_nhds (by linarith))
  have hq' : ∀ᶠ n in atTop, (s+t)/2 < (q n : ℝ) := hq.eventually (lt_mem_nhds (by linarith))
  apply radon_measure_le_of_nonneg_tests
  intro f hfn
  have hplim : Tendsto (fun n => ∫ z, f z ∂μ (p n)) atTop (𝓝 (∫ z, f z ∂M s)) := by
    simpa only [Function.comp_def,hrat] using (hcont f).continuousAt.tendsto.comp hp
  have hqlim : Tendsto (fun n => ∫ z, f z ∂μ (q n)) atTop (𝓝 (∫ z, f z ∂M t)) := by
    simpa only [Function.comp_def,hrat] using (hcont f).continuousAt.tendsto.comp hq
  apply le_of_tendsto_of_tendsto hplim hqlim
  filter_upwards [hp',hq'] with n hpn hqn
  let : (μ (q n)).Regular := H.regular (q n)
  exact integral_mono_measure (H.monotone (Rat.cast_le.mp (le_of_lt (hpn.trans hqn))))
    (ae_of_all _ hfn) f.integrable

/-- Agreement at rational times identifies continuous Radon families.
Thus the reconstruction is independent of compact exhaustions. -/
theorem halfPlane_continuous_measure_extension_unique
    (M N : ℝ → Measure upperHalfPlane)
    (hMr : ∀ t, (M t).Regular) (hNr : ∀ t, (N t).Regular)
    (hMc : ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂M t))
    (hNc : ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂N t))
    (heq : ∀ q : ℚ, M q = N q) : M = N := by
  funext t
  let : (M t).Regular := hMr t
  let : (N t).Regular := hNr t
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  obtain ⟨q,hq⟩ := exists_rational_sequence_tendsto t
  have hm := (hMc f).continuousAt.tendsto.comp hq
  have hn := (hNc f).continuousAt.tendsto.comp hq
  simp only [Function.comp_def,heq] at hm hn
  exact tendsto_nhds_unique hm hn

end SLEExactGauge

end

end OAI

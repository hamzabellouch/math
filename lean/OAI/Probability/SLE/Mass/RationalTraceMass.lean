import OAI.Probability.SLE.Mass.RationalTraceMassControl
import Mathlib.Topology.Sequences

namespace OAI

/-! Continuous extension of a rational measure family whose positive
increments are supported on the corresponding trace intervals. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology CompactlySupported ENNReal

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- This is the positive-increment and interval-support assertion used in
the pathwise extension. Local applications restrict all measures to one
compact set, making the terminal measure finite. -/
structure RationalTraceIncrements (μ : ℚ → Measure X) (ν : Measure X) (γ : ℝ → X) : Prop where
  regular : ∀ q, (μ q).Regular
  dominated : ∀ q, μ q ≤ ν
  increment : ∀ p q, p ≤ q → ∃ η : Measure X,
    μ q=μ p+η ∧ η ≤ ν.restrict (γ '' Icc (p:ℝ) q)

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
lemma RationalTraceIncrements.monotone {μ : ℚ → Measure X} {ν : Measure X} {γ : ℝ → X}
    (H : RationalTraceIncrements μ ν γ) : Monotone μ := by
  intro p q hpq
  obtain ⟨η,hη,_⟩ := H.increment p q hpq
  rw [hη]
  exact Measure.le_add_right le_rfl

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma RationalTraceIncrements.integral_dist_le {μ : ℚ → Measure X} {ν : Measure X}
    [IsFiniteMeasure ν] {γ : ℝ → X} (H : RationalTraceIncrements μ ν γ)
    (f : C_c(X,ℝ)) (p q : ℚ) :
    dist (∫ x, f x ∂μ p) (∫ x, f x ∂μ q) ≤ ‖f.toBoundedContinuousFunction‖ *
      (ν (γ '' Icc (min (p:ℝ) q) (max (p:ℝ) q))).toReal := by
  have ordered (a b : ℚ) (hab : a ≤ b) :
      dist (∫ x, f x ∂μ a) (∫ x, f x ∂μ b) ≤ ‖f.toBoundedContinuousFunction‖ *
        (ν (γ '' Icc (a:ℝ) b)).toReal := by
    obtain ⟨η,hη,hην⟩ := H.increment a b hab
    have hηle : η ≤ ν := hην.trans Measure.restrict_le_self
    let : IsFiniteMeasure η := isFiniteMeasure_of_le ν hηle
    let : (μ a).Regular := H.regular a
    rw [hη,integral_add_measure f.integrable f.integrable,dist_eq_norm]
    have hsub : (∫ x, f x ∂μ a)-((∫ x, f x ∂μ a)+(∫ x, f x ∂η))= -(∫ x, f x ∂η) := by ring
    rw [hsub,norm_neg]
    have hb := norm_integral_le_of_norm_le_const (μ := η)
      (ae_of_all η (fun x => f.toBoundedContinuousFunction.norm_coe_le_norm x))
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply ENNReal.toReal_mono (measure_ne_top ν _)
    exact (hην univ).trans_eq (by simp)
  rcases le_total p q with h | h
  · simpa only [min_eq_left (Rat.cast_le.mpr h),max_eq_right (Rat.cast_le.mpr h)] using ordered p q h
  · rw [dist_comm]
    simpa only [min_eq_right (Rat.cast_le.mpr h),max_eq_left (Rat.cast_le.mpr h)] using ordered q p h

lemma exists_rational_sequence_tendsto (t : ℝ) :
    ∃ q : ℕ → ℚ, Tendsto (fun n => (q n : ℝ)) atTop (𝓝 t) := by
  obtain ⟨x,hx,ht⟩ := mem_closure_iff_seq_limit.mp (Rat.denseRange_cast t)
  choose q hq using hx
  exact ⟨q,by simpa only [hq] using ht⟩

omit [SecondCountableTopology X] in
/-- The rational family has an all-real-time regular extension, continuous
against every compact continuous test. It is dominated by the same finite
terminal measure, and agrees exactly at every rational time. -/
theorem RationalTraceIncrements.exists_continuous_extension
    {μ : ℚ → Measure X} {ν : Measure X} [ν.Regular] [IsFiniteMeasure ν]
    [NullSingletonClass ν] {γ : ℝ → X} (H : RationalTraceIncrements μ ν γ)
    (hγ : Continuous γ) :
    ∃ M : ℝ → Measure X, (∀ t, (M t).Regular) ∧ (∀ t, M t ≤ ν) ∧
      (∀ q : ℚ, M q=μ q) ∧
      (∀ f : C_c(X,ℝ), Continuous (fun t => ∫ x, f x ∂M t)) ∧ Monotone M := by
  have hf (f : C_c(X,ℝ)) := continuous_rational_extension_of_trace_control
    ν γ hγ (fun q => ∫ x, f x ∂μ q) ‖f.toBoundedContinuousFunction‖ (norm_nonneg _)
    (H.integral_dist_le f)
  choose F hFc hFq _ using hf
  have hex (t : ℝ) : ∃ η : Measure X, η.Regular ∧ IsFiniteMeasureOnCompacts η ∧
      ∀ f : C_c(X,ℝ), (∫ x, f x ∂η)=F f t := by
    obtain ⟨q,hq⟩ := exists_rational_sequence_tendsto t
    let (n : ℕ) : (μ (q n)).Regular := H.regular (q n)
    have hlim (f : C_c(X,ℝ)) : Tendsto (fun n => ∫ x, f x ∂μ (q n)) atTop (𝓝 (F f t)) := by
      simpa only [Function.comp_def,hFq] using (hFc f).continuousAt.tendsto.comp hq
    obtain ⟨η,hηr,hηf,hηlim⟩ := radon_limit_of_all_test_limits (fun n => μ (q n))
      (fun f => ⟨F f t,hlim f⟩)
    exact ⟨η,hηr,hηf,fun f => tendsto_nhds_unique (hηlim f) (hlim f)⟩
  choose M hMr hMf hMI using hex
  have hcont (f : C_c(X,ℝ)) : Continuous (fun t => ∫ x, f x ∂M t) := by
    simpa only [hMI] using hFc f
  have hrat (q : ℚ) : M q=μ q := by
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
    have hlim : Tendsto (fun n => ∫ x, f x ∂μ (q n)) atTop (𝓝 (∫ x, f x ∂M t)) := by
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
  have hp' : ∀ᶠ n in atTop, (p n : ℝ)<(s+t)/2 := hp.eventually (gt_mem_nhds (by linarith))
  have hq' : ∀ᶠ n in atTop, (s+t)/2<(q n : ℝ) := hq.eventually (lt_mem_nhds (by linarith))
  apply radon_measure_le_of_nonneg_tests
  intro f hfn
  have hplim : Tendsto (fun n => ∫ x, f x ∂μ (p n)) atTop (𝓝 (∫ x, f x ∂M s)) := by
    simpa only [Function.comp_def,hrat] using (hcont f).continuousAt.tendsto.comp hp
  have hqlim : Tendsto (fun n => ∫ x, f x ∂μ (q n)) atTop (𝓝 (∫ x, f x ∂M t)) := by
    simpa only [Function.comp_def,hrat] using (hcont f).continuousAt.tendsto.comp hq
  apply le_of_tendsto_of_tendsto hplim hqlim
  filter_upwards [hp',hq'] with n hpn hqn
  let : (μ (q n)).Regular := H.regular (q n)
  exact integral_mono_measure (H.monotone (Rat.cast_le.mp (le_of_lt (hpn.trans hqn))))
    (ae_of_all _ hfn) f.integrable

end SLEExactGauge

end

end OAI

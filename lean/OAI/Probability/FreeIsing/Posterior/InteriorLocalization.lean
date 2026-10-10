import OAI.Probability.FreeIsing.Estimates.MessageFunction
import OAI.Probability.FreeIsing.Posterior.Limit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.PosteriorInteriorLocalization

theorem field_bound_iff_tanh_bounds {m X K : ℝ} :
    (m ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh m - X| ≤ K) ↔
      (Real.tanh (X - K) ≤ m ∧ m ≤ Real.tanh (X + K)) := by
  constructor
  · rintro ⟨hm, hb⟩
    constructor
    · apply (Real.artanh_le_artanh_iff
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩ hm).mp
      rw [Real.artanh_tanh]
      linarith [(abs_le.mp hb).1]
    · apply (Real.artanh_le_artanh_iff hm
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).mp
      rw [Real.artanh_tanh]
      linarith [(abs_le.mp hb).2]
  · intro hb
    have h := posterior_field_limit_of_tanh_bounds
      (u := fun _ : ℕ => m) tendsto_const_nhds (fun _ => hb)
    exact ⟨h.1, h.2.1⟩

private theorem continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_tanh_response t).continuousAt

theorem ae_all_field_bound_of_continuous
    {T Ω : Type*} [TopologicalSpace T] [SeparableSpace T]
    [MeasurableSpace Ω] {P : Measure Ω} {M X : T → Ω → ℝ} {K : ℝ}
    (hM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hb : ∀ t, ∀ᵐ ω ∂P,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K) :
    ∀ᵐ ω ∂P, ∀ t,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense T
  let : Countable S := hSc.to_subtype
  have hS : ∀ᵐ ω ∂P, ∀ t : S,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K :=
    ae_all_iff.mpr (fun t => hb t)
  filter_upwards [hM, hX, hS] with ω hMω hXω hSω
  have hall : ∀ t, Real.tanh (X t ω - K) ≤ M t ω ∧
      M t ω ≤ Real.tanh (X t ω + K) := by
    refine isClosed_property hSd.denseRange_val
      (p := fun t => Real.tanh (X t ω - K) ≤ M t ω ∧
        M t ω ≤ Real.tanh (X t ω + K)) ?_ ?_
    · exact (isClosed_le (continuous_tanh.comp (hXω.sub continuous_const)) hMω).inter
        (isClosed_le hMω (continuous_tanh.comp (hXω.add continuous_const)))
    · intro t
      exact field_bound_iff_tanh_bounds.mp (hSω t)
  exact fun t => field_bound_iff_tanh_bounds.mpr (hall t)

theorem continuous_artanh_of_interior
    {T : Type*} [TopologicalSpace T] {m : T → ℝ}
    (hm : Continuous m) (hi : ∀ t, m t ∈ Set.Ioo (-1 : ℝ) 1) :
    Continuous (fun t => Real.artanh (m t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_artanh_interval (hi t)).continuousAt.comp (hm.continuousAt)

theorem exists_uniform_radius_of_compact
    {T : Type*} [TopologicalSpace T] {s : Set T} (hs : IsCompact s)
    {m : T → ℝ} (hm : ContinuousOn m s)
    (hi : ∀ t ∈ s, m t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ t ∈ s, |m t| ≤ r := by
  by_cases hne : s.Nonempty
  · obtain ⟨t, ht, hmax⟩ := hs.exists_isMaxOn hne hm.abs
    exact ⟨|m t|, abs_nonneg _, abs_lt.mpr (hi t ht), fun u hu => hmax hu⟩
  · exact ⟨0, le_rfl, by norm_num, fun t ht => (hne ⟨t, ht⟩).elim⟩

theorem inverse_variance_le_of_abs_le {m r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hm : |m| ≤ r) :
    0 < 1 - r ^ 2 ∧ 0 < 1 - m ^ 2 ∧
      (1 - m ^ 2)⁻¹ ≤ (1 - r ^ 2)⁻¹ := by
  have hr : 0 < 1 - r ^ 2 := by nlinarith
  have hsq : m ^ 2 ≤ r ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg m) hr0).mpr hm
    simpa only [sq_abs] using h
  have hmpos : 0 < 1 - m ^ 2 := by linarith
  exact ⟨hr, hmpos, inv_anti₀ hr (by linarith)⟩

def radius (n : ℕ) : ℝ := 1 - ((n : ℝ) + 2)⁻¹

theorem radius_nonneg (n : ℕ) : 0 ≤ radius n := by
  have hp : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hi : ((n : ℝ) + 2)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one hp]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact sub_nonneg.mpr hi

theorem radius_lt_one (n : ℕ) : radius n < 1 := by
  have hp : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
  unfold radius
  linarith

theorem radius_monotone : Monotone radius := by
  intro n m hnm
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hi := inv_anti₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)
    (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by linarith)
  unfold radius
  linarith

theorem tendsto_radius : Tendsto radius atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hden
  change Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 1)
  simpa only [sub_zero, Function.comp_def] using
    tendsto_const_nhds.sub hi

theorem eventually_uniform_abs_lt_radius
    {T : Type*} [TopologicalSpace T] {s : Set T} (hs : IsCompact s)
    {m : T → ℝ} (hm : ContinuousOn m s)
    (hi : ∀ t ∈ s, m t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ n in atTop, ∀ t ∈ s, |m t| < radius n := by
  obtain ⟨r, _, hr, hb⟩ := exists_uniform_radius_of_compact hs hm hi
  filter_upwards [tendsto_radius.eventually_const_lt hr] with n hn
  exact fun t ht => (hb t ht).trans_lt hn

theorem ae_compact_localization_of_field_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M X : ℝ≥0 → Ω → ℝ} {K : ℝ}
    (hM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hb : ∀ t, ∀ᵐ ω ∂P,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop,
      ∀ t ≤ T, |M t ω| < radius n := by
  filter_upwards [hM, ae_all_field_bound_of_continuous hM hX hb] with ω hMω hbω
  intro T
  have h := eventually_uniform_abs_lt_radius
    (s := Set.Icc (0 : ℝ≥0) T) isCompact_Icc hMω.continuousOn
    (fun t _ => (hbω t).1)
  filter_upwards [h] with n hn
  exact fun t ht => hn t ⟨bot_le, ht⟩

def sampledRadiusEvent {T Ω : Type*} (q : ℕ → T) (M : T → Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ k : ℕ, |M (q k) ω| ≤ radius n}

theorem measurableSet_sampledRadiusEvent
    {T Ω : Type*} [MeasurableSpace Ω] (q : ℕ → T) (M : T → Ω → ℝ)
    (hM : ∀ t, Measurable (M t)) (n : ℕ) :
    MeasurableSet (sampledRadiusEvent q M n) := by
  simp only [sampledRadiusEvent, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => measurableSet_le (hM (q k)).abs measurable_const

theorem sampledRadiusEvent_monotone
    {T Ω : Type*} (q : ℕ → T) (M : T → Ω → ℝ) :
    Monotone (sampledRadiusEvent q M) := by
  intro n m hnm ω hω k
  exact (hω k).trans (radius_monotone hnm)

theorem mem_sampledRadiusEvent_iff
    {T Ω : Type*} [TopologicalSpace T] {q : ℕ → T} (hq : DenseRange q)
    {M : T → Ω → ℝ} {ω : Ω} (hM : Continuous (fun t => M t ω)) (n : ℕ) :
    ω ∈ sampledRadiusEvent q M n ↔ ∀ t, |M t ω| ≤ radius n := by
  constructor
  · intro h
    exact isClosed_property hq (isClosed_le hM.abs continuous_const) h
  · exact fun h k => h (q k)

theorem ae_mem_iUnion_sampledRadiusEvent
    {T Ω : Type*} [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace Ω] {P : Measure Ω} (q : ℕ → T) {M : T → Ω → ℝ}
    (hM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hi : ∀ᵐ ω ∂P, ∀ t, M t ω ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᵐ ω ∂P, ω ∈ ⋃ n, sampledRadiusEvent q M n := by
  filter_upwards [hM, hi] with ω hMω hiω
  obtain ⟨n, hn⟩ := (eventually_uniform_abs_lt_radius
    (s := Set.univ) isCompact_univ hMω.continuousOn (fun t _ => hiω t)).exists
  exact Set.mem_iUnion.mpr ⟨n, fun k => (hn (q k) (Set.mem_univ _)).le⟩

theorem tendsto_measure_sampledRadiusEvent
    {T Ω : Type*} [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace Ω] {P : Measure Ω} (q : ℕ → T) {M : T → Ω → ℝ}
    (hM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hi : ∀ᵐ ω ∂P, ∀ t, M t ω ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun n => P (sampledRadiusEvent q M n)) atTop (𝓝 (P Set.univ)) := by
  have hfull : P (⋃ n, sampledRadiusEvent q M n) = P Set.univ := by
    apply measure_congr
    filter_upwards [ae_mem_iUnion_sampledRadiusEvent q hM hi] with ω hω
    exact propext ⟨fun _ => Set.mem_univ ω, fun _ => hω⟩
  simpa only [Function.comp_def, hfull] using
    (tendsto_measure_iUnion_atTop (μ := P) (sampledRadiusEvent_monotone q M))

theorem tendsto_measure_compl_sampledRadiusEvent
    {T Ω : Type*} [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (q : ℕ → T) {M : T → Ω → ℝ} (hm : ∀ t, Measurable (M t))
    (hM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hi : ∀ᵐ ω ∂P, ∀ t, M t ω ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun n => P (sampledRadiusEvent q M n)ᶜ) atTop (𝓝 0) := by
  have hzero : P (⋂ n, (sampledRadiusEvent q M n)ᶜ) = 0 := by
    rw [← Set.compl_iUnion]
    exact ae_iff.mp (ae_mem_iUnion_sampledRadiusEvent q hM hi)
  have hanti : Antitone (fun n => (sampledRadiusEvent q M n)ᶜ) := by
    intro n m hnm
    exact Set.compl_subset_compl.mpr (sampledRadiusEvent_monotone q M hnm)
  simpa only [Function.comp_def, hzero] using
    (tendsto_measure_iInter_atTop
      (fun n => (measurableSet_sampledRadiusEvent q M hm n).compl.nullMeasurableSet)
      hanti ⟨0, measure_ne_top P _⟩)

end Problem367.PosteriorInteriorLocalization

end

end OAI

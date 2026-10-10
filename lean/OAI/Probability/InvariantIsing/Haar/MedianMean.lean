import OAI.Probability.InvariantIsing.Pressure.AlmostSure

namespace OAI

/-! Relating the deterministic medians and means in the concentration step. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

lemma abs_median_le_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (m B : ℝ)
    (hB : ∀ ω, |f ω| ≤ B)
    (hl : (1 / 2 : ℝ) ≤ μ.real {ω | f ω ≤ m})
    (hu : (1 / 2 : ℝ) ≤ μ.real {ω | m ≤ f ω}) : |m| ≤ B := by
  apply abs_le.mpr
  constructor
  · by_contra h
    have hm : m < -B := lt_of_not_ge h
    have he : {ω | f ω ≤ m} = (∅ : Set Ω) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      change f ω ≤ m at hω
      have hf := (abs_le.mp (hB ω)).1
      linarith
    rw [he] at hl
    norm_num at hl
  · by_contra h
    have hm : B < m := lt_of_not_ge h
    have he : {ω | m ≤ f ω} = (∅ : Set Ω) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      change m ≤ f ω at hω
      have hf := (abs_le.mp (hB ω)).2
      linarith
    rw [he] at hu
    norm_num at hu

/-- A bounded deviation has mean at most r plus its bound times the r-tail. -/
lemma abs_integral_sub_le_deviation_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfi : Integrable f μ) (m B r : ℝ) (hr : 0 ≤ r)
    (hB : ∀ ω, |f ω - m| ≤ B) :
    |(∫ ω, f ω ∂μ) - m| ≤ r + B * μ.real {ω | r ≤ |f ω - m|} := by
  let A : Set Ω := {ω | r ≤ |f ω - m|}
  have hA : MeasurableSet A := measurableSet_le measurable_const (hf.sub_const m).abs
  have hiA : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  have hupper : Integrable (fun ω => r + B * A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const r).add (hiA.const_mul B)
  have he (ω : Ω) : |f ω - m| ≤ r + B * A.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, mul_one]
      linarith [hB ω]
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact (lt_of_not_ge hω).le
  calc
    _ = |∫ ω, f ω - m ∂μ| := by rw [integral_sub hfi (integrable_const m)]; simp
    _ ≤ ∫ ω, |f ω - m| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => f ω - m)
    _ ≤ ∫ ω, r + B * A.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      integral_mono (hfi.sub (integrable_const m)).abs hupper he
    _ = r + B * μ.real A := by
      rw [integral_add (integrable_const r) (hiA.const_mul B), integral_const_mul,
        integral_indicator_const 1 hA]
      simp

/-- Uniformly bounded observables with exponential tails about their medians
have means and medians asymptotically equal. -/
theorem tendsto_mean_sub_median_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (m : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ n ω, |f n ω| ≤ B)
    (hl : ∀ n, (1 / 2 : ℝ) ≤ μ.real {ω | f n ω ≤ m n})
    (hu : ∀ n, (1 / 2 : ℝ) ≤ μ.real {ω | m n ≤ f n ω})
    (htail : ∀ r : ℝ, 0 < r → ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
      ∀ n, μ.real {ω | r ≤ |f n ω - m n|} ≤ C * Real.exp (-a * (n : ℝ))) :
    Tendsto (fun n => (∫ ω, f n ω ∂μ) - m n) atTop (𝓝 0) := by
  have hi (n : ℕ) : Integrable (f n) μ :=
    (integrable_const B).mono' (hf n).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hbound n ω)
  have hm (n : ℕ) : |m n| ≤ B := abs_median_le_bound μ (f n) (m n) B (hbound n) (hl n) (hu n)
  have hdev (n : ℕ) (ω : Ω) : |f n ω - m n| ≤ 2 * B := by
    have hs := (abs_sub _ _).trans (add_le_add (hbound n ω) (hm n))
    linarith
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨C, a, hC, ha, ht⟩ := htail (ε / 2) (by positivity)
  have hlim : Tendsto (fun n : ℕ => ε / 2 + 2 * B * (C * Real.exp (-a * (n : ℝ))))
      atTop (𝓝 (ε / 2)) := by
    have hlin : Tendsto (fun n : ℕ => -a * (n : ℝ)) atTop atBot :=
      by simpa only [Function.comp_def, neg_mul] using
        tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
    have he := (Real.tendsto_exp_atBot.comp hlin).const_mul C
    simpa using (he.const_mul (2 * B)).const_add (ε / 2)
  have hevent : ∀ᶠ n : ℕ in atTop, ε / 2 + 2 * B * (C * Real.exp (-a * (n : ℝ))) < ε :=
    hlim.eventually (gt_mem_nhds (by linarith : ε / 2 < ε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, ?_⟩
  intro n hn
  have hb := abs_integral_sub_le_deviation_tail μ (f n) (hf n) (hi n) (m n) (2 * B)
    (ε / 2) (by positivity) (hdev n)
  have hb' := hb.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (ht n) (by positivity : 0 ≤ 2 * B)))
  simpa only [Real.dist_eq, sub_zero] using hb'.trans_lt (hN n hn)

end InvariantIsing

end

end OAI

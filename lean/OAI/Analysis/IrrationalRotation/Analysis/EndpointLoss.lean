import Mathlib

namespace OAI

open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace

namespace Invariant233.EndpointLoss

variable {X : Type*} [MeasurableSpace X]

theorem sqrt_integral_sq_eq_norm {μ : Measure X} (f : Lp ℝ 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖f‖ := by
  have hs : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [hs, Real.sqrt_sq (norm_nonneg f)]

theorem sqrt_integral_sq_eq_toReal_eLpNorm {μ : Measure X} {h : X → ℝ} (hh : MemLp h 2 μ) :
    Real.sqrt (∫ x, h x ^ 2 ∂μ) = (eLpNorm h 2 μ).toReal := by
  rw [← Lp.norm_toLp h hh, ← sqrt_integral_sq_eq_norm]
  congr 1
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp] with x hx
  rw [hx]

theorem tendsto_measure_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x)
    {t : ℕ → ℝ} (ht_mono : Antitone t)
    (ht_zero : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => μ {x | r x < t n}) atTop (𝓝 0) := by
  let s : ℕ → Set X := fun n => {x | r x < t n}
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_lt hr measurable_const
  have hm : Antitone s := by
    intro n m hnm x hx
    exact lt_of_lt_of_le hx (ht_mono hnm)
  have hnull : μ (⋂ n, s n) = 0 := by
    apply measure_mono_null (t := {x | ¬ 0 < r x})
    · intro x hx
      simp only [mem_iInter, mem_ofPred_eq, s] at hx ⊢
      have hle : r x ≤ 0 := ge_of_tendsto' ht_zero (fun n => (hx n).le)
      exact not_lt.mpr hle
    · exact ae_iff.mp hpos
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (hs n).nullMeasurableSet) hm ⟨0, measure_ne_top μ _⟩
  simpa only [hnull, Function.comp_def, s] using hlim

theorem tendsto_measureReal_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x)
    {t : ℕ → ℝ} (ht_mono : Antitone t)
    (ht_zero : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => μ.real {x | r x < t n}) atTop (𝓝 0) := by
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_measure_sublevel_zero μ hr hpos ht_mono ht_zero)

theorem tendsto_measureReal_reciprocal_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x) :
    Tendsto (fun n : ℕ => μ.real {x | r x < 1 / ((n : ℝ) + 1)})
      atTop (𝓝 0) := by
  apply tendsto_measureReal_sublevel_zero μ hr hpos
  · intro n m hnm
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem setIntegral_density_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (∫ x in s, h x ∂μ) ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two h_nonneg
    (show 0 ≤ᵐ[μ] s.indicator (fun _ : X => (1 : ℝ)) from
      Filter.Eventually.of_forall (fun x => by
        change 0 ≤ s.indicator (fun _ : X => (1 : ℝ)) x
        by_cases hx : x ∈ s <;> simp [hx]))
    (by simpa using hh) (by simpa using (MemLp.indicator hs (memLp_const (1 : ℝ))))
  have hmul : (fun x => h x * s.indicator (fun _ : X => (1 : ℝ)) x) =
      s.indicator h := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hpow : (fun x => (s.indicator (fun _ : X => (1 : ℝ)) x) ^ (2 : ℝ)) =
      s.indicator (fun _ : X => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hmul, integral_indicator hs, hpow] at hCS
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have hmass : (∫ x, s.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = μ.real s := by
    rw [integral_indicator hs]
    simp
  simpa only [hmass] using hCS

theorem withDensity_measureReal_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).real s ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  rw [measureReal_def, withDensity_apply _ hs]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_restrict_of_ae h_nonneg) hh.aestronglyMeasurable.restrict]
  exact setIntegral_density_le_sqrt μ hh h_nonneg hs

theorem tendsto_measureReal_of_uniform_sqrt_bound
    (μ : Measure X) (ν : ℕ → Measure X) (H : ℝ) {s : ℕ → Set X}
    (hbound : ∀ n, (ν n).real (s n) ≤ H * Real.sqrt (μ.real (s n)))
    (hzero : Tendsto (fun n => μ.real (s n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ν n).real (s n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) hbound
  simpa using tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp hzero)

theorem tendsto_measureReal_one_div_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x) :
    Tendsto (fun n : ℕ => μ.real {x | r x < 1 / (n : ℝ)})
      atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using
    tendsto_measureReal_reciprocal_sublevel_zero μ hr hpos

theorem tendsto_withDensity_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x)
    (h : ℕ → X → ℝ) (hh : ∀ n, MemLp (h n) 2 μ)
    (h_nonneg : ∀ n, 0 ≤ᵐ[μ] h n) (H : ℝ)
    (hbound : ∀ n, Real.sqrt (∫ x, h n x ^ 2 ∂μ) ≤ H) :
    Tendsto (fun n : ℕ =>
      (μ.withDensity (fun x => ENNReal.ofReal (h n x))).real
        {x | r x < 1 / (n : ℝ)}) atTop (𝓝 0) := by
  apply tendsto_measureReal_of_uniform_sqrt_bound μ _ H
  · intro n
    exact (withDensity_measureReal_le_sqrt μ (hh n) (h_nonneg n)
      (measurableSet_lt hr measurable_const)).trans
      (mul_le_mul_of_nonneg_right (hbound n) (Real.sqrt_nonneg _))
  · exact tendsto_measureReal_one_div_sublevel_zero μ hr hpos

theorem tendsto_two_endpoint_losses_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hinterior : ∀ᵐ x ∂μ, 0 < r x ∧ r x < 1)
    (h₁ h₂ : ℕ → X → ℝ)
    (hh₁ : ∀ n, MemLp (h₁ n) 2 μ) (hh₂ : ∀ n, MemLp (h₂ n) 2 μ)
    (hn₁ : ∀ n, 0 ≤ᵐ[μ] h₁ n) (hn₂ : ∀ n, 0 ≤ᵐ[μ] h₂ n)
    (H₁ H₂ : ℝ)
    (hb₁ : ∀ n, Real.sqrt (∫ x, h₁ n x ^ 2 ∂μ) ≤ H₁)
    (hb₂ : ∀ n, Real.sqrt (∫ x, h₂ n x ^ 2 ∂μ) ≤ H₂) :
    Tendsto (fun n : ℕ =>
      (μ.withDensity (fun x => ENNReal.ofReal (h₁ n x))).real
        {x | r x < 1 / (n : ℝ)} +
      (μ.withDensity (fun x => ENNReal.ofReal (h₂ n x))).real
        {x | 1 - r x < 1 / (n : ℝ)}) atTop (𝓝 0) := by
  have hp : ∀ᵐ x ∂μ, 0 < r x := hinterior.mono (fun _ hx => hx.1)
  have hq : ∀ᵐ x ∂μ, 0 < 1 - r x := hinterior.mono (fun _ hx => sub_pos.mpr hx.2)
  simpa only [zero_add, Pi.sub_apply] using
    (tendsto_withDensity_sublevel_zero μ hr hp h₁ hh₁ hn₁ H₁ hb₁).add
      (tendsto_withDensity_sublevel_zero μ (measurable_const.sub hr) hq
        h₂ hh₂ hn₂ H₂ hb₂)

theorem tendsto_pullback_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) (x : (n : ℕ) → Ω n → X)
    (hx : ∀ n, Measurable (x n))
    (h : ℕ → X → ℝ) (hh : ∀ n, MemLp (h n) 2 μ)
    (hn : ∀ n, 0 ≤ᵐ[μ] h n) (H : ℝ)
    (hb : ∀ n, Real.sqrt (∫ z, h n z ^ 2 ∂μ) ≤ H)
    (hmap : ∀ n, (P n).map (x n) =
      μ.withDensity (fun z => ENNReal.ofReal (h n z))) :
    Tendsto (fun n : ℕ => (P n).real {ω | r (x n ω) < 1 / (n : ℝ)})
      atTop (𝓝 0) := by
  have ht := tendsto_withDensity_sublevel_zero μ hr hpos h hh hn H hb
  convert ht using 1
  funext n
  rw [← hmap n, map_measureReal_apply (hx n) (measurableSet_lt hr measurable_const)]
  rfl

theorem tendsto_endpoint_bad_union_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hi : ∀ᵐ z ∂μ, 0 < r z ∧ r z < 1)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n))
    (x y : (n : ℕ) → Ω n → X)
    (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n))
    (h₁ h₂ : ℕ → X → ℝ)
    (hh₁ : ∀ n, MemLp (h₁ n) 2 μ) (hh₂ : ∀ n, MemLp (h₂ n) 2 μ)
    (hn₁ : ∀ n, 0 ≤ᵐ[μ] h₁ n) (hn₂ : ∀ n, 0 ≤ᵐ[μ] h₂ n)
    (H₁ H₂ : ℝ)
    (hb₁ : ∀ n, Real.sqrt (∫ z, h₁ n z ^ 2 ∂μ) ≤ H₁)
    (hb₂ : ∀ n, Real.sqrt (∫ z, h₂ n z ^ 2 ∂μ) ≤ H₂)
    (hm₁ : ∀ n, (P n).map (x n) =
      μ.withDensity (fun z => ENNReal.ofReal (h₁ n z)))
    (hm₂ : ∀ n, (P n).map (y n) =
      μ.withDensity (fun z => ENNReal.ofReal (h₂ n z))) :
    Tendsto (fun n : ℕ => (P n).real
      ({ω | r (x n ω) < 1 / (n : ℝ)} ∪
       {ω | 1 - r (y n ω) < 1 / (n : ℝ)})) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun _ => measureReal_union_le _ _)
  have hp : ∀ᵐ z ∂μ, 0 < r z := hi.mono (fun _ hz => hz.1)
  have hq : ∀ᵐ z ∂μ, 0 < 1 - r z := hi.mono (fun _ hz => sub_pos.mpr hz.2)
  simpa only [zero_add, Pi.sub_apply] using
    (tendsto_pullback_sublevel_zero μ hr hp P x hx h₁ hh₁ hn₁ H₁ hb₁ hm₁).add
      (tendsto_pullback_sublevel_zero μ (measurable_const.sub hr) hq
        P y hy h₂ hh₂ hn₂ H₂ hb₂ hm₂)

end Invariant233.EndpointLoss

end OAI

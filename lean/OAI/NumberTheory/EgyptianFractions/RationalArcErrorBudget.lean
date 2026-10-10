import OAI.NumberTheory.EgyptianFractions.RationalArcVolume

namespace OAI
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace Problem337.ThreePrimeAnalysis

/-- Explicit logarithmic budget for the cubic approximation error. A cutoff
and radius of logarithmic size cost two powers of the logarithmic parameter. -/
theorem norm_integral_cubic_majorArc_error_logbudget
    {N C a b δ : ℝ} (Q : ℕ) (hN : 1 < N) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hQ : (Q : ℝ) ≤ (Real.log N) ^ b)
    (hδN : δ ≤ (Real.log N) ^ b / N)
    {E : Set ℝ} (hE : E ⊆ majorArcUnion Q δ) (f g phase : ℝ → ℂ)
    (hf : ∀ x ∈ E, ‖f x‖ ≤ C * N)
    (hg : ∀ x ∈ E, ‖g x‖ ≤ C * N)
    (herr : ∀ x ∈ E, ‖f x - g x‖ ≤ N / (Real.log N) ^ a)
    (hphase : ∀ x ∈ E, ‖phase x‖ ≤ 1) :
    ‖∫ x in E, (f x ^ 3 - g x ^ 3) * phase x‖ ≤
      12 * C ^ 2 * N ^ 2 * (Real.log N) ^ (2 * b - a) := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  have ha : 0 < (Real.log N) ^ a := Real.rpow_pos_of_pos hlog a
  have hb : 0 < (Real.log N) ^ b := Real.rpow_pos_of_pos hlog b
  have hbase := norm_integral_cubic_majorArc_error_le Q hδ
    (mul_nonneg hC hN0.le) (div_pos hN0 ha).le hE f g phase hf hg herr hphase
  calc
    _ ≤ 12 * (Q : ℝ) * δ * (C * N) ^ 2 * (N / (Real.log N) ^ a) := hbase
    _ ≤ 12 * (Real.log N) ^ b * ((Real.log N) ^ b / N) *
        (C * N) ^ 2 * (N / (Real.log N) ^ a) := by
      gcongr
    _ = 12 * C ^ 2 * N ^ 2 * (Real.log N) ^ (2 * b - a) := by
      rw [Real.rpow_sub hlog]
      have hdouble : (Real.log N) ^ (2 * b) = ((Real.log N) ^ b) ^ 2 := by
        rw [show 2 * b = b + b by ring, Real.rpow_add hlog]
        ring
      rw [hdouble]
      field_simp

/-- The logarithmic major-arc error factor tends to zero whenever the
approximation saves more than twice the logarithmic cutoff exponent. -/
theorem tendsto_majorArc_log_error_factor (C a b : ℝ) (hab : 2 * b < a) :
    Tendsto (fun N : ℝ => 12 * C ^ 2 * (Real.log N) ^ (2 * b - a))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
    Real.tendsto_log_atTop
  have h' := h.const_mul (12 * C ^ 2)
  simpa only [neg_sub, mul_zero, Function.comp_def] using h'

/-- Uniform little-o form, with all arc sets and complex approximants quantified
after the threshold. This consumes pointwise approximation estimates but does
not assert any prime-distribution estimate. -/
theorem eventually_norm_integral_cubic_majorArc_error_le
    (C a b ε : ℝ) (hC : 0 ≤ C) (hab : 2 * b < a) (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop, ∀ (Q : ℕ) (δ : ℝ), 0 ≤ δ →
      (Q : ℝ) ≤ (Real.log N) ^ b → δ ≤ (Real.log N) ^ b / N →
      ∀ (E : Set ℝ), E ⊆ majorArcUnion Q δ →
      ∀ (f g phase : ℝ → ℂ),
      (∀ x ∈ E, ‖f x‖ ≤ C * N) →
      (∀ x ∈ E, ‖g x‖ ≤ C * N) →
      (∀ x ∈ E, ‖f x - g x‖ ≤ N / (Real.log N) ^ a) →
      (∀ x ∈ E, ‖phase x‖ ≤ 1) →
      ‖∫ x in E, (f x ^ 3 - g x ^ 3) * phase x‖ ≤ ε * N ^ 2 := by
  have hsmall := (tendsto_majorArc_log_error_factor C a b hab).eventually
    (gt_mem_nhds hε)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with N hsmall hN
  intro Q δ hδ hQ hδN E hE f g phase hf hg herr hphase
  have hbound := norm_integral_cubic_majorArc_error_logbudget Q hN hC hδ
    hQ hδN hE f g phase hf hg herr hphase
  calc
    _ ≤ 12 * C ^ 2 * N ^ 2 * (Real.log N) ^ (2 * b - a) := hbound
    _ = (12 * C ^ 2 * (Real.log N) ^ (2 * b - a)) * N ^ 2 := by ring
    _ ≤ ε * N ^ 2 := mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg N)

/-- Function-valued little-o conclusion for a moving major-arc set. The complex
integral error is negligible compared with the quadratic main-term scale. -/
theorem cubic_majorArc_error_isLittleO
    (C a b : ℝ) (hC : 0 ≤ C) (hab : 2 * b < a)
    (Q : ℝ → ℕ) (δ : ℝ → ℝ) (E : ℝ → Set ℝ)
    (f g phase : ℝ → ℝ → ℂ)
    (hwindow : ∀ᶠ N : ℝ in atTop,
      0 ≤ δ N ∧ (Q N : ℝ) ≤ (Real.log N) ^ b ∧
      δ N ≤ (Real.log N) ^ b / N ∧ E N ⊆ majorArcUnion (Q N) (δ N) ∧
      (∀ x ∈ E N, ‖f N x‖ ≤ C * N) ∧
      (∀ x ∈ E N, ‖g N x‖ ≤ C * N) ∧
      (∀ x ∈ E N, ‖f N x - g N x‖ ≤ N / (Real.log N) ^ a) ∧
      (∀ x ∈ E N, ‖phase N x‖ ≤ 1)) :
    (fun N : ℝ => ∫ x in E N, (f N x ^ 3 - g N x ^ 3) * phase N x)
      =o[atTop] (fun N : ℝ => N ^ 2) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [eventually_norm_integral_cubic_majorArc_error_le C a b ε
    hC hab hε, hwindow] with N hN hw
  obtain ⟨hδ, hQ, hδN, hE, hf, hg, herr, hphase⟩ := hw
  have hb := hN (Q N) (δ N) hδ hQ hδN (E N) hE
    (f N) (g N) (phase N) hf hg herr hphase
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg N)] using hb

end Problem337.ThreePrimeAnalysis

end

end OAI

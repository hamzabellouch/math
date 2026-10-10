import OAI.MathematicalPhysics.DefocusingNLS.Profile.NormalizedSlowDerivative

namespace OAI

/-! # Continuous extension of the normalized slow solution at inverse radius zero -/

open Filter Topology Set

namespace DefocusingNLS

noncomputable def compactifiedSlowSolution (q : ℂ) (m : ℕ) (x : ℂ) (t : ℝ) : ℂ :=
  if t = 0 then 1 else normalizedSlowSolution q m (x / (t : ℂ))

@[simp] theorem compactifiedSlowSolution_zero (q : ℂ) (m : ℕ) (x : ℂ) :
    compactifiedSlowSolution q m x 0 = 1 := by simp [compactifiedSlowSolution]

theorem compactifiedSlowSolution_pos (q : ℂ) (m : ℕ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    compactifiedSlowSolution q m x t = normalizedSlowSolution q m (x / (t : ℂ)) := by
  simp [compactifiedSlowSolution, ht.ne']

theorem slow_div_real_re_nonneg {x : ℂ} {t : ℝ} (hx : 0 ≤ x.re) (ht : 0 < t) :
    0 ≤ (x / (t : ℂ)).re := by
  simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, add_zero]
  exact div_nonneg (mul_nonneg hx ht.le) (Complex.normSq_nonneg _)

theorem continuousWithinAt_compactifiedSlowSolution_zero (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    ContinuousWithinAt (compactifiedSlowSolution q m x) (Ioi 0) 0 := by
  obtain ⟨A, hA, hb⟩ := regularizedSlowSolution_first_remainder q m hq
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖compactifiedSlowSolution q m x t - 1‖ ≤ (A / ‖x‖) * t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hxn).filter_mono nhdsWithin_le_nhds] with t ht htx
    rw [compactifiedSlowSolution_pos q m x ht]
    have hn : 1 ≤ ‖x / (t : ℂ)‖ := by
      rw [norm_div, Complex.norm_of_nonneg ht.le]
      exact (le_div_iff₀ ht).mpr (by linarith)
    have hh := hb (x / (t : ℂ)) (slow_div_real_re_nonneg hx ht) hn
    apply hh.trans_eq
    rw [norm_div, Complex.norm_of_nonneg ht.le]
    field_simp
  have hz : Tendsto (fun t : ℝ => (A / ‖x‖) * t) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => (A / ‖x‖) * t) := continuous_const.mul continuous_id
    simpa only [mul_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hh := (squeeze_zero_norm' hbound hz).add_const (1 : ℂ)
  rw [ContinuousWithinAt, compactifiedSlowSolution_zero]
  simpa only [sub_add_cancel, zero_add] using hh

theorem continuousAt_compactifiedSlowSolution_pos (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (compactifiedSlowSolution q m x) t := by
  have hy := slow_div_real_re_nonneg hx ht
  have hy0 : x / (t : ℂ) ≠ 0 := div_ne_zero hx0 (Complex.ofReal_ne_zero.mpr ht.ne')
  have hnorm := (hasDerivAt_normalizedSlowSolution q m (x / (t : ℂ)) hq hy hy0).continuousAt
  have harg : ContinuousAt (fun u : ℝ => x / (u : ℂ)) t :=
    continuousAt_const.div Complex.continuous_ofReal.continuousAt
      (Complex.ofReal_ne_zero.mpr ht.ne')
  have he : compactifiedSlowSolution q m x =ᶠ[𝓝 t]
      (fun u : ℝ => normalizedSlowSolution q m (x / (u : ℂ))) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact compactifiedSlowSolution_pos q m x hu
  exact (ContinuousAt.comp (f := fun u : ℝ => x / (u : ℂ))
    (g := normalizedSlowSolution q m) hnorm harg).congr
      (by simpa only [Function.comp_def] using he.symm)

theorem continuousOn_compactifiedSlowSolution (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    ContinuousOn (compactifiedSlowSolution q m x) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with he | ht
  · subst t
    rw [ContinuousWithinAt, ← Ioi_union_left, nhdsWithin_union]
    have h0 := continuousWithinAt_compactifiedSlowSolution_zero q m x hq hx hx0
    rw [ContinuousWithinAt] at h0
    exact h0.sup (by simpa only [nhdsWithin_singleton] using
      tendsto_pure_nhds (compactifiedSlowSolution q m x) (0 : ℝ))
  · exact (continuousAt_compactifiedSlowSolution_pos q m x hq hx hx0 ht).continuousWithinAt

end DefocusingNLS

end OAI

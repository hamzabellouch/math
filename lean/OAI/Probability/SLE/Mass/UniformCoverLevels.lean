import OAI.Probability.SLE.Gauge.CoverRadiusLevels
import OAI.Probability.SLE.Gauge.CoverGrid

namespace OAI

/-! Uniform clock geometry over the moving grid centers retained above a
fixed positive height. The terminal visit level is separated from every
test endpoint by a full clock unit. -/

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def coverVisitLevel (z : ℂ) (T : ℝ) (n : ℕ) : ℝ :=
  Real.log (2 * z.im) + T * (n : ℝ) - Real.log (512 * Real.pi)

/-- One deterministic cutoff works for every point above the retained height
and every test index, including the endpoint after the last test. -/
theorem eventually_uniform_cover_levels {T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, η / 2 ≤ z.im →
      (∀ j : ℕ, n / 3 ≤ j →
        coverLogLevel z T j = Real.log (2 * z.im) + T * (j : ℝ)) ∧
      coverLogLevel z T (2 * n / 3 + 1) + 1 ≤ coverVisitLevel z T n ∧
      4 * coverRadius T n ≤ z.im := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log η / T)
  have hNT : -Real.log η < T * (N : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hT).mp hN
  have hlarge : ∀ᶠ n : ℕ in atTop,
      3 * (Real.log (512 * Real.pi) + 1 + T) / T ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hlim : Tendsto (fun n => 4 * coverRadius T n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (coverRadius_tendsto_zero hT).const_mul 4
  have hsmall : ∀ᶠ n : ℕ in atTop, 4 * coverRadius T n < η / 2 :=
    hlim.eventually (gt_mem_nhds (half_pos hη))
  filter_upwards [eventually_ge_atTop (3 * N), hlarge, hsmall] with n hn hnlarge hnsmall
  intro z hz
  have hlog : Real.log η ≤ Real.log (2 * z.im) :=
    Real.log_le_log hη (by linarith)
  have hlevels : ∀ j : ℕ, n / 3 ≤ j →
      coverLogLevel z T j = Real.log (2 * z.im) + T * (j : ℝ) := by
    intro j hj
    have hjN : N ≤ j := by omega
    have hNj : T * (N : ℝ) ≤ T * (j : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hjN) hT.le
    exact max_eq_right (by linarith)
  refine ⟨hlevels, ?_, hnsmall.le.trans hz⟩
  rw [hlevels (2 * n / 3 + 1) (by omega)]
  have hlast : 3 * (2 * n / 3 + 1) ≤ 2 * n + 3 := by omega
  have hlastR : (3 : ℝ) * (2 * n / 3 + 1 : ℕ) ≤ 2 * n + 3 := by exact_mod_cast hlast
  have hnT := (div_le_iff₀ hT).mp hnlarge
  unfold coverVisitLevel
  nlinarith

lemma coverVisitLevel_nonneg_of_gap (z : ℂ) (T : ℝ) (n : ℕ)
    (hgap : coverLogLevel z T (2 * n / 3 + 1) + 1 ≤ coverVisitLevel z T n) :
    0 ≤ coverVisitLevel z T n := by
  have h0 := coverLogLevel_nonneg z T (2 * n / 3 + 1)
  linarith

/-- The late visit level is the fixed multiple `512π r_n` of the fine mesh,
independently of the varying center's height. -/
lemma coverVisitLevel_radius (z : ℂ) (hz : 0 < z.im) (T : ℝ) (n : ℕ) :
    (2 * z.im) * Real.exp (-coverVisitLevel z T n) =
      (512 * Real.pi) * coverRadius T n := by
  have hz2 : 0 < 2 * z.im := by positivity
  have hM : 0 < 512 * Real.pi := by positivity
  have he : -coverVisitLevel z T n = Real.log (512 * Real.pi) +
      (-Real.log (2 * z.im) + -T * (n : ℝ)) := by
    unfold coverVisitLevel
    ring
  unfold coverRadius
  rw [he, Real.exp_add, Real.exp_add,
    Real.exp_log hM, Real.exp_neg, Real.exp_log hz2]
  field_simp [hz2.ne']

/-- The exact test window inherits the common late-grid cutoff. -/
theorem eventually_uniform_cover_window_levels {T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, η / 2 ≤ z.im →
      (∀ j ∈ coverTestWindow n,
        coverLogLevel z T j = Real.log (2 * z.im) + T * (j : ℝ)) ∧
      coverLogLevel z T (2 * n / 3 + 1) =
        Real.log (2 * z.im) + T * ((2 * n / 3 + 1 : ℕ) : ℝ) ∧
      coverLogLevel z T (2 * n / 3 + 1) + 1 ≤ coverVisitLevel z T n ∧
      4 * coverRadius T n ≤ z.im := by
  filter_upwards [eventually_uniform_cover_levels hT hη] with n hn
  intro z hz
  obtain ⟨hlevel, hgap, hsmall⟩ := hn z hz
  exact ⟨fun j hj => hlevel j (Finset.mem_Icc.mp hj).1,
    hlevel _ (by omega), hgap, hsmall⟩

/-- In particular the changing retained grid centers satisfy all clock and
visit geometry simultaneously; no center-dependent cutoff is required. -/
theorem eventually_retained_grid_cover_levels {R T η : ℝ} {K : Set ℂ}
    (hT : 0 < T) (hη : 0 < η) (hK : K ⊆ Metric.closedBall 0 R)
    (hheight : ∀ z ∈ K, η ≤ z.im) :
    ∀ᶠ n : ℕ in atTop, ∀ ij ∈ retainedCoverGridIndex R (coverRadius T n) K,
      let z := coverGridCenter (coverRadius T n) ij
      z ∈ upperHalfPlane ∧
      (∀ j ∈ coverTestWindow n,
        coverLogLevel z T j = Real.log (2 * z.im) + T * (j : ℝ)) ∧
      coverLogLevel z T (2 * n / 3 + 1) =
        Real.log (2 * z.im) + T * ((2 * n / 3 + 1 : ℕ) : ℝ) ∧
      coverLogLevel z T (2 * n / 3 + 1) + 1 ≤ coverVisitLevel z T n ∧
      4 * coverRadius T n ≤ z.im := by
  have hsmall := (coverRadius_tendsto_zero hT).eventually (gt_mem_nhds (show 0 < η / 4 by positivity))
  filter_upwards [eventually_uniform_cover_window_levels hT hη, hsmall] with n hn hnr
  intro ij hij
  have hcenter := (retainedCoverGrid_center_bounds hK hheight hij).2
  have hz : η / 2 ≤ (coverGridCenter (coverRadius T n) ij).im := by linarith
  exact ⟨lt_of_lt_of_le (half_pos hη) hz, hn _ hz⟩

end SLEExactGauge

end

end OAI

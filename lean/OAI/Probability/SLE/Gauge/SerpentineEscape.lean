import OAI.Probability.SLE.Gauge.SerpentineCompleteCurve

namespace OAI

/-! The final linear tail and bounded normal displacement of the
complete serpentine. These supply properness of the ribbon chart. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine

lemma complete_linear_tail (m : ℕ) (H r X Y : ℝ) {t : ℝ}
    (ht : connectorEntry H r X Y + columnEntry 0 m (2 * m) + 1 ≤ t) :
    completeSpine m H r X Y t = ((X + 200 * m : ℝ) : ℂ) +
      ((Y + t - connectorEntry H r X Y - columnEntry 0 m (2 * m) : ℝ) : ℂ) * Complex.I ∧
    completeTangent m H r X Y t = Complex.I := by
  have hc : 0 ≤ columnEntry 0 m (2 * m) := by unfold columnEntry; positivity
  have htA : connectorEntry H r X Y < t := by linarith
  have htC : columnEntry 0 m (2 * m) ≤ t - connectorEntry H r X Y := by linarith
  simp only [completeSpine, completeTangent, curveJoin_of_gt htA]
  rw [arraySpine_tail m (2 * m) htC, arrayTangent_tail m (2 * m) htC]
  constructor
  · apply Complex.ext <;>
      simp only [arrayCenter, straightPiece, side_even, one_mul, Nat.cast_mul, Nat.cast_ofNat,
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  · simp only [straightTangent, side_even, Complex.ofReal_one, one_mul]

lemma complete_eventually_ray (m : ℕ) (H r X Y : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      completeSpine m H r X Y t = completeSpine m H r X Y T + ((t - T : ℝ) : ℂ) * Complex.I := by
  let T := max 0 (connectorEntry H r X Y + columnEntry 0 m (2 * m) + 1)
  have hT : connectorEntry H r X Y + columnEntry 0 m (2 * m) + 1 ≤ T := le_max_right _ _
  refine ⟨T, le_max_left _ _, fun t ht => ?_⟩
  rw [(complete_linear_tail m H r X Y (hT.trans ht)).1,
    (complete_linear_tail m H r X Y hT).1]
  push_cast
  ring

lemma completeSpine_escape (m : ℕ) (H r X Y : ℝ) :
    Tendsto (completeSpine m H r X Y) atTop (cocompact ℂ) := by
  have him : Tendsto (fun t => (completeSpine m H r X Y t).im) atTop atTop := by
    have hh : Tendsto (fun t : ℝ => Y + t - connectorEntry H r X Y - columnEntry 0 m (2 * m))
        atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using
        tendsto_atTop_add_const_right atTop (-columnEntry 0 m (2 * m))
          (tendsto_atTop_add_const_right atTop (-connectorEntry H r X Y)
            (tendsto_atTop_add_const_left atTop Y tendsto_id))
    apply hh.congr'
    filter_upwards [eventually_ge_atTop
      (connectorEntry H r X Y + columnEntry 0 m (2 * m) + 1)] with t ht
    rw [(complete_linear_tail m H r X Y ht).1]
    simp
  have hn : Tendsto (fun t => ‖completeSpine m H r X Y t‖) atTop atTop := by
    apply tendsto_atTop_mono (fun t => ?_) him
    exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
  apply tendsto_cocompact_of_tendsto_dist_comp_atTop 0
  simpa only [dist_zero_right] using hn

lemma complete_normal_displacement (m : ℕ) (H r X Y : ℝ) {z : ℂ} (hz : |z.im| ≤ 1) :
    dist (normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) z)
      (completeSpine m H r X Y z.re) ≤ 1 := by
  rw [normalRibbon, dist_self_add_left, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, completeTangent_norm, mul_one, mul_one]
  exact hz

lemma complete_normal_width (m : ℕ) (H r X Y : ℝ) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) z -
      completeSpine m H r X Y z.re‖ ≤ 1 := by
  simpa only [dist_eq_norm] using complete_normal_displacement m H r X Y hz

lemma complete_normal_continuous {H r X Y : ℝ} (m : ℕ) (hr : 50 ≤ r)
    (hX : 2 * r < X) (hY : H + 2 * r < Y) :
    Continuous (normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y)) := by
  have hr0 : 0 < r := by linarith
  have hσ : Continuous (completeSpine m H r X Y) :=
    continuous_iff_continuousAt.mpr (fun t => (completeSpine_hasDerivAt m hr0 hX hY t).continuousAt)
  have hT : Continuous (completeTangent m H r X Y) :=
    (completeTangent_lipschitz m hr hX hY).continuous
  exact (hσ.comp Complex.continuous_re).add
    (((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const).mul
      (hT.comp Complex.continuous_re))

end SLEExactGauge.Serpentine

end

end OAI

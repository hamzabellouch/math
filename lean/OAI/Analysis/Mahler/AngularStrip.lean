import OAI.Analysis.Mahler.AngularEndpoint

namespace OAI

/-! Real-part image and real preimages of the conformal map. -/

noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped Topology
namespace MahlerConformal

lemma F_real_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < (F (r : ℂ)).re := by
  have h := Q_mem_Ioo hr hr1 Real.pi_div_two_pos (by linarith [Real.pi_pos])
  rw [Q_pi_div_two] at h
  exact h.2

lemma F_real_lt_one {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : (F (r : ℂ)).re < 1 := by
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := B r) (g := fun _ => 2/Real.pi) Real.pi_pos (continuous_B r).continuousOn
    continuous_const.continuousOn (fun θ _ => (B_lt_two_div_pi r θ).le)
    ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, B_lt_two_div_pi r 0⟩
  rw [integral_B_semicircle hr hr1] at hi
  have he : (∫ _θ in (0 : ℝ)..Real.pi, 2/Real.pi) = 2 := by
    simp [intervalIntegral.integral_const, smul_eq_mul, Real.pi_ne_zero]
  rw [he] at hi
  linarith

lemma polar_neg_angle (r θ : ℝ) : polar r (-θ) = starRingEnd ℂ (polar r θ) := by
  apply Complex.ext <;> simp [polar_re, polar_im, Real.cos_neg, Real.sin_neg]

lemma Q_neg_angle (r θ : ℝ) : Q r (-θ) = Q r θ := by
  simp only [Q, polar_neg_angle, F_conj, Complex.conj_re]

lemma Q_mem_Icc {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) :
    Q r θ ∈ Icc (-(F (r : ℂ)).re) (F (r : ℂ)).re := by
  have ha := (Q_strictAntiOn hr hr1).antitoneOn
  exact ⟨by simpa only [Q_pi] using ha hθ ⟨Real.pi_pos.le, le_rfl⟩ hθ.2,
    by simpa only [Q_zero] using ha ⟨le_rfl, Real.pi_pos.le⟩ hθ hθ.1⟩

/-- Every image point has real part in the strip. -/
theorem F_re_mem_strip {w : ℂ} (hw : ‖w‖ < 1) : (F w).re ∈ Ioo (-1 : ℝ) 1 := by
  by_cases hw0 : w = 0
  · simp [hw0, F_zero]
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hp : polar ‖w‖ w.arg = w := Complex.norm_mul_exp_arg_mul_I w
  have hθ : |w.arg| ∈ Icc (0 : ℝ) Real.pi := by
    refine ⟨abs_nonneg _, abs_le.mpr ⟨?_, Complex.arg_le_pi w⟩⟩
    exact (Complex.neg_pi_lt_arg w).le
  have he : Q ‖w‖ |w.arg| = (F w).re := by
    rcases le_total 0 w.arg with h | h
    · rw [abs_of_nonneg h, Q, hp]
    · rw [abs_of_nonpos h, Q_neg_angle, Q, hp]
  have hb := Q_mem_Icc hr hw hθ
  rw [he] at hb
  have hm := F_real_lt_one hr hw
  constructor <;> linarith [hb.1, hb.2]

/-- Every strip real part has its unique angular preimage for all sufficiently
large radii below one. No radial monotonicity theorem is assumed. -/
theorem eventually_existsUnique_angle {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    ∀ᶠ r : ℝ in 𝓝[<] 1, ∃! θ : ℝ, θ ∈ Ioo 0 Real.pi ∧ Q r θ = q := by
  have hqa : |q| < 1 := abs_lt.mpr ⟨by linarith [hq.1], hq.2⟩
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1, |q| < (F (r : ℂ)).re :=
    F_real_tendsto_one.eventually (eventually_gt_nhds hqa)
  filter_upwards [eventually_radius, he] with r hr h
  exact existsUnique_angle hr.1 hr.2 (by linarith [neg_abs_le q]) (lt_of_le_of_lt (le_abs_self q) h)

lemma continuousOn_F_real {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fun t : ℝ => (F (t : ℂ)).re) (Icc 0 r) := by
  intro t ht
  have hw : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans_lt hr1
  exact (hasDerivAt_F_series hw).real_of_complex.continuousAt.continuousWithinAt

/-- Every point on the real interval (-1,1) is the actual value F(t) at a real
point t in the disk. This is existence only; it does not assert univalence. -/
theorem exists_real_preimage {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    ∃ t : ℝ, t ∈ Ioo (-1 : ℝ) 1 ∧ F (t : ℂ) = (q : ℂ) := by
  have hqa : |q| < 1 := abs_lt.mpr ⟨by linarith [hq.1], hq.2⟩
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo 0 1 ∧ |q| < (F (r : ℂ)).re :=
    eventually_radius.and (F_real_tendsto_one.eventually (eventually_gt_nhds hqa))
  obtain ⟨r, hr, hqr⟩ := he.exists
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc hr.1.le (continuousOn_F_real hr.1.le hr.2)
    (show |q| ∈ Icc (F (0 : ℂ)).re (F (r : ℂ)).re by simpa [F_zero] using And.intro (abs_nonneg q) hqr.le)
  have hF : F (t : ℂ) = ((|q| : ℝ) : ℂ) := by
    apply Complex.ext
    · exact hte
    · simpa using F_real_im t
  by_cases hq0 : 0 ≤ q
  · refine ⟨t, ⟨by linarith [ht.1], ht.2.trans_lt hr.2⟩, ?_⟩
    simpa only [abs_of_nonneg hq0] using hF
  · refine ⟨-t, ⟨by linarith [ht.2, hr.2], by linarith [ht.1]⟩, ?_⟩
    rw [Complex.ofReal_neg, F_odd, hF, abs_of_neg (lt_of_not_ge hq0)]
    simp

/-- The set of real parts of the image is exactly (-1,1).
This does not assert that each vertical fiber is an interval. -/
theorem image_re_F_disk : Complex.re '' (F '' ball (0 : ℂ) 1) = Ioo (-1 : ℝ) 1 := by
  ext q
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    exact F_re_mem_strip (by simpa using hw)
  · intro hq
    obtain ⟨t, ht, hF⟩ := exists_real_preimage hq
    refine ⟨(q : ℂ), ⟨(t : ℂ), ?_, hF⟩, by simp⟩
    simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩

end MahlerConformal

end

end OAI

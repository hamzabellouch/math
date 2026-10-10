import OAI.Probability.SLE.KernelConsistency

namespace OAI

/-! The interaction of two active points in the September 25 manuscript,
equation `mp:interaction-derivative`.  Centering by a common real driver
does not change the kernel, so differentiability of that driver is not
needed for the ordinary Loewner-path calculation. -/

noncomputable section
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal

namespace SLEExactGauge.Multipoint

def interaction (z w : ℂ) : ℝ := halfPlaneGreen z w

lemma interaction_eq (z w : ℂ) :
    interaction z w = Real.log ‖(z - conj w) / (z - w)‖ := rfl

lemma interaction_nonneg {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 ≤ interaction z w := halfPlaneGreen_nonneg hz hw

lemma interaction_center (z w : ℂ) (u : ℝ) :
    interaction (z - (u : ℂ)) (w - (u : ℂ)) = interaction z w := by
  have hn : z - (u : ℂ) - conj (w - (u : ℂ)) = z - conj w := by
    simp only [map_sub, Complex.conj_ofReal]
    ring
  have hd : z - (u : ℂ) - (w - (u : ℂ)) = z - w := by ring
  unfold interaction halfPlaneGreen
  rw [hn, hd]

/-- The real-part identity behind the interaction derivative. -/
lemma interaction_velocity_algebra (a : ℝ) (z w : ℂ) :
    (-(a : ℂ) / (z * conj w) + (a : ℂ) / (z * w)).re =
      -2 * a * (z.im / ‖z‖ ^ 2) * (w.im / ‖w‖ ^ 2) := by
  simp only [Complex.add_re, Complex.div_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_mul, Complex.normSq_conj, Complex.sq_norm]
  ring

lemma interaction_difference_algebra (a : ℝ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) (hne : z ≠ w) :
    (((a : ℂ) / z - conj ((a : ℂ) / w)) / (z - conj w) -
      ((a : ℂ) / z - (a : ℂ) / w) / (z - w)).re =
        -2 * a * (z.im / ‖z‖ ^ 2) * (w.im / ‖w‖ ^ 2) := by
  have hz0 : z ≠ 0 := fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hz
  have hw0 : w ≠ 0 := fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hw
  have hcw0 : conj w ≠ 0 := by simpa using hw0
  have hn : z - w ≠ 0 := sub_ne_zero.mpr hne
  have hnc : z - conj w ≠ 0 := by
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.conj_im] at hi
    linarith
  have h₁ : ((a : ℂ) / z - conj ((a : ℂ) / w)) / (z - conj w) =
      -(a : ℂ) / (z * conj w) := by
    simp only [map_div₀, Complex.conj_ofReal]
    field_simp
    ring
  have h₂ : ((a : ℂ) / z - (a : ℂ) / w) / (z - w) =
      -(a : ℂ) / (z * w) := by
    field_simp
    ring
  rw [h₁, h₂]
  simpa only [neg_div, sub_neg_eq_add] using interaction_velocity_algebra a z w

/-- Two differentiable paths with a common real drift have the source's
interaction derivative; the common drift cancels in both differences. -/
theorem interaction_hasDerivWithinAt
    {f g : ℝ → ℂ} {S : Set ℝ} {t a b : ℝ}
    (hf : HasDerivWithinAt f ((a : ℂ) / f t + (b : ℂ)) S t)
    (hg : HasDerivWithinAt g ((a : ℂ) / g t + (b : ℂ)) S t)
    (hfi : 0 < (f t).im) (hgi : 0 < (g t).im) (hne : f t ≠ g t) :
    HasDerivWithinAt (fun s => interaction (f s) (g s))
      (-2 * a * ((f t).im / ‖f t‖ ^ 2) * ((g t).im / ‖g t‖ ^ 2)) S t := by
  have hn : f t - g t ≠ 0 := sub_ne_zero.mpr hne
  have hnc : f t - conj (g t) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.conj_im] at hi
    linarith
  have hd := hasDerivWithinAt_log_norm_div
    (hf.sub (hasDerivWithinAt_conj hg)) (hf.sub hg) hnc hn
  apply hd.congr_deriv
  change (((a : ℂ) / f t + (b : ℂ) - conj ((a : ℂ) / g t + (b : ℂ))) /
    (f t - conj (g t)) -
    ((a : ℂ) / f t + (b : ℂ) - ((a : ℂ) / g t + (b : ℂ))) /
      (f t - g t)).re = _
  simp only [map_add, Complex.conj_ofReal]
  have h₁ : (a : ℂ) / f t + (b : ℂ) - (conj ((a : ℂ) / g t) + (b : ℂ)) =
      (a : ℂ) / f t - conj ((a : ℂ) / g t) := by ring
  have h₂ : (a : ℂ) / f t + (b : ℂ) - ((a : ℂ) / g t + (b : ℂ)) =
      (a : ℂ) / f t - (a : ℂ) / g t := by ring
  rw [h₁, h₂]
  exact interaction_difference_algebra a hfi hgi hne

theorem interaction_hasDerivAt
    {f g : ℝ → ℂ} {t a b : ℝ}
    (hf : HasDerivAt f ((a : ℂ) / f t + (b : ℂ)) t)
    (hg : HasDerivAt g ((a : ℂ) / g t + (b : ℂ)) t)
    (hfi : 0 < (f t).im) (hgi : 0 < (g t).im) (hne : f t ≠ g t) :
    HasDerivAt (fun s => interaction (f s) (g s))
      (-2 * a * ((f t).im / ‖f t‖ ^ 2) * ((g t).im / ‖g t‖ ^ 2)) t :=
  (interaction_hasDerivWithinAt hf.hasDerivWithinAt hg.hasDerivWithinAt hfi hgi hne
    (S := univ)).hasDerivAt (univ_mem)

/-- The driver can be any real function here: only the two uncentered
Loewner paths are differentiated. -/
theorem centered_interaction_hasDerivWithinAt
    {f g : ℝ → ℂ} (U : ℝ → ℝ) {S : Set ℝ} {t a : ℝ}
    (hf : HasDerivWithinAt f ((a : ℂ) / (f t - (U t : ℂ))) S t)
    (hg : HasDerivWithinAt g ((a : ℂ) / (g t - (U t : ℂ))) S t)
    (hfi : 0 < (f t).im) (hgi : 0 < (g t).im) (hne : f t ≠ g t) :
    HasDerivWithinAt
      (fun s => interaction (f s - (U s : ℂ)) (g s - (U s : ℂ)))
      (-2 * a * ((f t).im / ‖f t - (U t : ℂ)‖ ^ 2) *
        ((g t).im / ‖g t - (U t : ℂ)‖ ^ 2)) S t := by
  have hn : f t - g t ≠ 0 := sub_ne_zero.mpr hne
  have hnc : f t - conj (g t) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.conj_im] at hi
    linarith
  have hd := hasDerivWithinAt_log_norm_div
    (hf.sub (hasDerivWithinAt_conj hg)) (hf.sub hg) hnc hn
  have h₁ : f t - conj (g t) =
      (f t - (U t : ℂ)) - conj (g t - (U t : ℂ)) := by
    simp only [map_sub, Complex.conj_ofReal]
    ring
  have h₂ : f t - g t = (f t - (U t : ℂ)) - (g t - (U t : ℂ)) := by ring
  have hd' : HasDerivWithinAt (fun s => interaction (f s) (g s))
      (-2 * a * ((f t).im / ‖f t - (U t : ℂ)‖ ^ 2) *
        ((g t).im / ‖g t - (U t : ℂ)‖ ^ 2)) S t := by
    apply hd.congr_deriv
    dsimp only [Pi.sub_apply]
    rw [h₁, h₂, interaction_difference_algebra a (by simpa using hfi)
      (by simpa using hgi) (sub_left_inj.not.mpr hne)]
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  simpa only [interaction_center] using hd'

theorem centered_interaction_hasDerivAt
    {f g : ℝ → ℂ} (U : ℝ → ℝ) {t a : ℝ}
    (hf : HasDerivAt f ((a : ℂ) / (f t - (U t : ℂ))) t)
    (hg : HasDerivAt g ((a : ℂ) / (g t - (U t : ℂ))) t)
    (hfi : 0 < (f t).im) (hgi : 0 < (g t).im) (hne : f t ≠ g t) :
    HasDerivAt
      (fun s => interaction (f s - (U s : ℂ)) (g s - (U s : ℂ)))
      (-2 * a * ((f t).im / ‖f t - (U t : ℂ)‖ ^ 2) *
        ((g t).im / ‖g t - (U t : ℂ)‖ ^ 2)) t :=
  (centered_interaction_hasDerivWithinAt U hf.hasDerivWithinAt hg.hasDerivWithinAt
    hfi hgi hne (S := univ)).hasDerivAt univ_mem

end SLEExactGauge.Multipoint

end

end OAI

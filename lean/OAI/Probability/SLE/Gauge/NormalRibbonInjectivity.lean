import OAI.Probability.SLE.Gauge.NormalRibbonPatch

namespace OAI

/-! A global chord bound and the local ribbon estimate rule out all
self-contacts of a width-one normal strip. -/

noncomputable section
open Set Metric
open scoped NNReal

namespace SLEExactGauge.Serpentine

theorem normalRibbon_injective_of_chord_bound (σ tangent : ℝ → ℂ)
    (hd : ∀ t, HasDerivAt σ (tangent t) t)
    (hunit : ∀ t, ‖tangent t‖ = 1)
    (hL : LipschitzWith (1 / 50) tangent)
    (hchord : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |s - t| ≤ 2 * ‖σ s - σ t‖) :
    InjOn (normalRibbon σ tangent) {z : ℂ | 0 ≤ z.re ∧ |z.im| ≤ 1} := by
  intro z hz w hw he
  have hnz : ‖(z.im : ℂ) * Complex.I * tangent z.re‖ ≤ 1 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      hunit, mul_one, mul_one]
    exact hz.2
  have hnw : ‖(w.im : ℂ) * Complex.I * tangent w.re‖ ≤ 1 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      hunit, mul_one, mul_one]
    exact hw.2
  have heq : σ z.re - σ w.re =
      (w.im : ℂ) * Complex.I * tangent w.re - (z.im : ℂ) * Complex.I * tangent z.re := by
    unfold normalRibbon at he
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using he)
  have hn : ‖σ z.re - σ w.re‖ ≤ 2 := by
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith)
  have hc : |z.re - w.re| ≤ 4 := (hchord _ _ hz.1 hw.1).trans (by linarith)
  have hab : max z.re w.re - min z.re w.re ≤ 4 := by
    rw [max_sub_min_eq_abs]
    simpa only [abs_sub_comm] using hc
  have hz' : z.re ∈ Icc (min z.re w.re) (max z.re w.re) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hw' : w.re ∈ Icc (min z.re w.re) (max z.re w.re) := ⟨min_le_right _ _, le_max_right _ _⟩
  have hlower := (normalRibbon_patch_bounds σ tangent _ _ hab
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hunit t) hL.lipschitzOnWith
    z w ⟨hz', hz.2⟩ ⟨hw', hw.2⟩).2
  rw [he, dist_self, mul_zero] at hlower
  exact dist_eq_zero.mp (le_antisymm hlower dist_nonneg)

end SLEExactGauge.Serpentine

end

end OAI

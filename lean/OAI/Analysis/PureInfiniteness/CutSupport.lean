import OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs

namespace OAI

/-! Fixed-cut action on a supported element, used for the return column in
KR02 Lemma 7.6.  A continuous divided difference avoids spectral projections
and works in a nonunital algebra. -/

noncomputable section

namespace WeakPureInfiniteness

def cutDifferenceRatio (δ t : ℝ) : ℝ :=
  min δ ((1 - δ) * t / max (1 - t) (1 - δ))

lemma continuous_cutDifferenceRatio {δ : ℝ} (hδ : δ < 1) :
    Continuous (cutDifferenceRatio δ) := by
  unfold cutDifferenceRatio
  apply continuous_const.min
  exact (continuous_const.mul continuous_id).div
    ((continuous_const.sub continuous_id).max continuous_const)
    (fun t => ne_of_gt (lt_of_lt_of_le (by linarith : 0 < 1 - δ) (le_max_right _ _)))

lemma cutDifferenceRatio_zero {δ : ℝ} (hδ : 0 ≤ δ) :
    cutDifferenceRatio δ 0 = 0 := by
  simp only [cutDifferenceRatio, mul_zero, zero_div, min_eq_right hδ]

lemma cutDifferenceRatio_identity {δ : ℝ} (hδ : δ < 1) (t : ℝ) :
    max (t - δ) 0 - (1 - δ) * t = cutDifferenceRatio δ t * t - cutDifferenceRatio δ t := by
  by_cases ht : t ≤ δ
  · have hd : 0 < 1 - t := by linarith
    have hq : (1 - δ) * t / (1 - t) ≤ δ := by
      apply (div_le_iff₀ hd).mpr
      nlinarith
    rw [cutDifferenceRatio, max_eq_left (by linarith : 1 - δ ≤ 1 - t),
      min_eq_right hq, max_eq_right (sub_nonpos.mpr ht)]
    field_simp
    ring
  · have ht' : δ ≤ t := le_of_not_ge ht
    rw [cutDifferenceRatio, max_eq_right (by linarith : 1 - t ≤ 1 - δ)]
    have hne : 1 - δ ≠ 0 := by linarith
    rw [mul_div_cancel_left₀ t hne, min_eq_left ht', max_eq_left (sub_nonneg.mpr ht')]
    ring

variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem cut_mul_of_mul_eq {f g : A} (hf : IsSelfAdjoint f) (hfg : f * g = g)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    MainGap.cut f δ * g = (1 - δ) • g := by
  let q := cutDifferenceRatio δ
  have hq := continuous_cutDifferenceRatio hδ1
  have hq0 := cutDifferenceRatio_zero hδ0
  have hcut0 : max (0 - δ) 0 = 0 := max_eq_right (by linarith)
  have hid : MainGap.cut f δ - (1 - δ) • f = cfcₙ q f * f - cfcₙ q f := by
    have hleft : cfcₙ (fun t : ℝ => max (t - δ) 0 - (1 - δ) * t) f =
        MainGap.cut f δ - (1 - δ) • f := by
      rw [cfcₙ_sub (fun t : ℝ => max (t - δ) 0) (fun t : ℝ => (1 - δ) * t) f
        (by fun_prop) hcut0 (by fun_prop) (by simp), cfcₙ_const_mul_id (1 - δ) f hf]
      rfl
    have hright : cfcₙ (fun t : ℝ => q t * t - q t) f = cfcₙ q f * f - cfcₙ q f := by
      rw [cfcₙ_sub (fun t : ℝ => q t * t) q f
        (hq.mul continuous_id).continuousOn (by simp) hq.continuousOn hq0,
        cfcₙ_mul q (fun t : ℝ => t) f hq.continuousOn hq0 continuousOn_id rfl,
        cfcₙ_id' ℝ f hf]
    rw [← hleft, ← hright]
    apply cfcₙ_congr
    intro t _
    exact cutDifferenceRatio_identity hδ1 t
  have hz : (MainGap.cut f δ - (1 - δ) • f) * g = 0 := by
    rw [hid, sub_mul, mul_assoc, hfg, sub_self]
  rw [sub_mul, smul_mul_assoc, hfg] at hz
  exact sub_eq_zero.mp hz

end WeakPureInfiniteness

end

end OAI

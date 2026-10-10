import Mathlib.Analysis.Complex.HasPrimitives

namespace OAI

/-! # Holomorphic gluing across one horizontal line

This is the local analytic bridge for extending a bounded KMS strip
whose two boundary values agree. Rectangular integrals split along the
line; Morera's theorem then gives holomorphicity across it.
-/

namespace KadisonKastler

open Complex Set MeasureTheory
open scoped Interval

noncomputable section

private theorem horizontal_rectangle_mem {a b : ℝ} {z w p : ℂ}
    (hz : a < z.im ∧ z.im < b) (hw : a < w.im ∧ w.im < b)
    (hp : p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) :
    a < p.im ∧ p.im < b := by
  exact ⟨(lt_min hz.1 hw.1).trans_le hp.2.1,
    hp.2.2.trans_lt (max_lt hz.2 hw.2)⟩

/-- Continuity and holomorphicity on both sides suffice across a horizontal seam. -/
theorem differentiableOn_horizontal_strip_glue
    {f : ℂ → ℂ} {a b s : ℝ} (has : a < s) (hsb : s < b)
    (hc : ContinuousOn f {z | a < z.im ∧ z.im < b})
    (hd : ∀ z, a < z.im → z.im < b → z.im ≠ s → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ f {z | a < z.im ∧ z.im < b} := by
  have hopen : IsOpen {z : ℂ | a < z.im ∧ z.im < b} :=
    (isOpen_Ioo.preimage continuous_im)
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hopen).mp
  refine ⟨?_, hc⟩
  intro z w hzw
  have hz : a < z.im ∧ z.im < b := hzw ⟨left_mem_uIcc, left_mem_uIcc⟩
  have hw : a < w.im ∧ w.im < b := hzw ⟨right_mem_uIcc, right_mem_uIcc⟩
  have hrect (v q : ℂ) (hv : a < v.im ∧ v.im < b)
      (hq : a < q.im ∧ q.im < b) (hseam : v.im = s ∨ q.im = s) :
      (∫ x : ℝ in v.re..q.re, f (x + v.im * I)) -
        (∫ x : ℝ in v.re..q.re, f (x + q.im * I)) +
        I * (∫ y : ℝ in v.im..q.im, f (q.re + y * I)) -
        I * (∫ y : ℝ in v.im..q.im, f (v.re + y * I)) = 0 := by
    apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f v q
      (hc.mono fun p hp => horizontal_rectangle_mem hv hq hp)
    intro p hp
    have hp' : a < p.im ∧ p.im < b :=
      ⟨(lt_min hv.1 hq.1).trans hp.2.1,
        hp.2.2.trans (max_lt hv.2 hq.2)⟩
    apply (hd p hp'.1 hp'.2 ?_).differentiableWithinAt
    intro hps
    rcases hseam with hvs | hqs
    · have hlo := hp.2.1
      have hhi := hp.2.2
      simp only [hps, hvs, min_lt_iff, lt_max_iff, lt_self_iff_false,
        false_or] at hlo hhi
      exact (lt_asymm hlo hhi)
    · have hlo := hp.2.1
      have hhi := hp.2.2
      simp only [hps, hqs, min_lt_iff, lt_max_iff, lt_self_iff_false,
        or_false] at hlo hhi
      exact (lt_asymm hlo hhi)
  have hint (r c d : ℝ) (hc' : a < c ∧ c < b) (hd' : a < d ∧ d < b) :
      IntervalIntegrable (fun y : ℝ => f (r + y * I)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    apply hc.comp (by fun_prop)
    intro y hy
    change a < (r + y * I : ℂ).im ∧ (r + y * I : ℂ).im < b
    simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add] using
      And.intro ((lt_min hc'.1 hd'.1).trans_le hy.1)
        (hy.2.trans_lt (max_lt hc'.2 hd'.2))
  have h₁ := hrect z (w.re + s * I) hz (by simpa using And.intro has hsb)
    (Or.inr (by simp))
  have h₂ := hrect (z.re + s * I) w (by simpa using And.intro has hsb) hw
    (Or.inl (by simp))
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add] at h₁ h₂
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint w.re z.im s hz ⟨has, hsb⟩)
      (hint w.re s w.im ⟨has, hsb⟩ hw),
    ← intervalIntegral.integral_add_adjacent_intervals (hint z.re z.im s hz ⟨has, hsb⟩)
      (hint z.re s w.im ⟨has, hsb⟩ hw)]
  simp only [smul_eq_mul, mul_add]
  linear_combination h₁ + h₂

end

end KadisonKastler

end OAI

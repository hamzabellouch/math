import Mathlib

namespace OAI

universe u_1 u_2

noncomputable section
open Filter
open scoped Topology

namespace Problem336AdditiveD139

theorem affine_stable_limit_root_im_nonpos {T : Type u_1} {l : Filter T} [l.NeBot]
    {A B : T → ℂ} {a b : ℂ}
    (hA : Tendsto A l (𝓝 a)) (hB : Tendsto B l (𝓝 b)) (hb : b ≠ 0)
    (hstable : ∀ᶠ t in l, ∀ z : ℂ, 0 < z.im → A t + B t * z ≠ 0) :
    (-a / b).im ≤ 0 := by
  have hlim : Tendsto (fun t => (-A t / B t).im) l (𝓝 ((-a / b).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp (hA.neg.div hB hb)
  apply le_of_tendsto hlim
  filter_upwards [hstable, hB.eventually_ne hb] with t ht hBt
  by_contra hpos
  have hz : 0 < (-A t / B t).im := lt_of_not_ge hpos
  apply ht (-A t / B t) hz
  field_simp
  ring

theorem real_affine_zero_of_upper_half_plane {a b : ℝ} {w : ℂ}
    (hw : 0 < w.im) (hzero : (a : ℂ) + (b : ℂ) * w = 0) :
    a = 0 ∧ b = 0 := by
  have him := congrArg Complex.im hzero
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_mul, add_zero, zero_add, Complex.zero_im] at him
  have hb : b = 0 := (mul_eq_zero.mp him).resolve_right (ne_of_gt hw)
  subst b
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_eq_zero] at hzero
  exact ⟨hzero, rfl⟩

theorem bivariate_stable_of_coefficientwise_limit
    {T : Type u_2} {l : Filter T} [l.NeBot]
    {A B C D : T → ℂ} {a b c d : ℝ}
    (ha : Tendsto A l (𝓝 (a : ℂ))) (hb : Tendsto B l (𝓝 (b : ℂ)))
    (hc : Tendsto C l (𝓝 (c : ℂ))) (hd : Tendsto D l (𝓝 (d : ℂ)))
    (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0)
    (hstable : ∀ᶠ t in l, ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      A t + B t * z + C t * w + D t * z * w ≠ 0) :
    ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      (a : ℂ) + (b : ℂ) * z + (c : ℂ) * w + (d : ℂ) * z * w ≠ 0 := by
  intro z w hz hw hzero
  have hzero' : ((a : ℂ) + (c : ℂ) * w) +
      ((b : ℂ) + (d : ℂ) * w) * z = 0 := by
    linear_combination hzero
  by_cases hden : (b : ℂ) + (d : ℂ) * w = 0
  · have hac : (a : ℂ) + (c : ℂ) * w = 0 := by simpa [hden] using hzero'
    obtain ⟨ha0, hc0⟩ := real_affine_zero_of_upper_half_plane hw hac
    obtain ⟨hb0, hd0⟩ := real_affine_zero_of_upper_half_plane hw hden
    simp_all
  · have hstab' : ∀ᶠ t in l, ∀ v : ℂ, 0 < v.im →
        (A t + C t * w) + (B t + D t * w) * v ≠ 0 := by
      filter_upwards [hstable] with t ht
      intro v hv heq
      apply ht v w hv hw
      linear_combination heq
    have hroot := affine_stable_limit_root_im_nonpos
      (ha.add (hc.mul_const w)) (hb.add (hd.mul_const w)) hden hstab'
    have hroot_eq : -((a : ℂ) + (c : ℂ) * w) /
        ((b : ℂ) + (d : ℂ) * w) = z := by
      apply (div_eq_iff hden).2
      linear_combination -hzero'
    rw [hroot_eq] at hroot
    exact (not_lt_of_ge hroot) hz

end Problem336AdditiveD139

end

end OAI

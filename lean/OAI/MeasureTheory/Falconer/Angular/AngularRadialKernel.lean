import OAI.MeasureTheory.Falconer.Radial.LinearRadialDecay

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem signed_distance_frequency {d₁ d₂ s₁ s₂ : ℝ} (h1 : 0 ≤ d₁) (h2 : 0 ≤ d₂)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) :
    |d₁-d₂| ≤ |s₁*d₁+s₂*d₂| := by
  have hh : |d₁-d₂| ≤ d₁+d₂ :=
    abs_le.mpr ⟨by linarith only [h1], by linarith only [h2]⟩
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl
  · simpa only [one_mul,abs_of_nonneg (add_nonneg h1 h2)] using hh
  · simp only [one_mul,neg_one_mul,← sub_eq_add_neg,le_refl]
  · rw [neg_one_mul,one_mul,show -d₁+d₂ = -(d₁-d₂) by ring,abs_neg]
  · rw [neg_one_mul,neg_one_mul,show -d₁+-d₂ = -(d₁+d₂) by ring,abs_neg,
      abs_of_nonneg (add_nonneg h1 h2)]
    exact hh

theorem noncomparable_radial_frequency {dlarge dsmall t s : ℝ}
    (hsep : 2*dsmall ≤ dlarge) (ht : |t| ≤ dsmall) (hs : s = 1 ∨ s = -1) :
    dlarge/2 ≤ |s*dlarge+t| := by
  obtain ⟨ht1,ht2⟩ := abs_le.mp ht
  rcases hs with rfl | rfl
  · simp only [one_mul]
    linarith only [hsep, ht1, le_abs_self (dlarge+t)]
  · simp only [neg_one_mul]
    linarith only [hsep, ht2, neg_le_abs (-dlarge+t)]

theorem angular_radial_kernel_bound {f : ℝ → ℂ} {C S R d₁ d₂ s₁ s₂ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc (1/4:ℝ) 4)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hR : 0 ≤ R) (h1 : 0 ≤ d₁) (h2 : 0 ≤ d₂)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (h0 : ∀ t, ‖f t‖ ≤ C*S) (hder : ∀ t, ‖iteratedDeriv 2 f t‖ ≤ C*S) :
    ‖radialPhaseIntegral f (R*(s₁*d₁+s₂*d₂))‖ ≤ 15*C*S/(1+R*|d₁-d₂|)^2 := by
  have hh := radialPhaseIntegral_two_derivatives hf hs (by norm_num) (mul_nonneg hC hS) h0 hder
    (xi := R*(s₁*d₁+s₂*d₂))
  have he : 4*(C*S)*((4:ℝ)-1/4) = 15*C*S := by ring
  rw [he] at hh
  apply hh.trans
  have hfreq : R*|d₁-d₂| ≤ |R*(s₁*d₁+s₂*d₂)| := by
    rw [abs_mul,abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left (signed_distance_frequency h1 h2 hs₁ hs₂) hR
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity) (add_le_add_right hfreq 1) 2

end PlanarFalconer

end OAI

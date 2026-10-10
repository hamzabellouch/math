import Mathlib

namespace OAI

open MeasureTheory

namespace Invariant233.UniformIntervalFourier

theorem norm_integral_exp_mul_I_le {ξ : ℝ} (hξ : ξ ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / |ξ| := by
  have hc : (ξ : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hξ) Complex.I_ne_zero
  have heq : (fun t : ℝ => Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)) =
      (fun t : ℝ => Complex.exp (((ξ : ℂ) * Complex.I) * t)) := by
    funext t
    congr 1
    push_cast
    ring
  have hn (t : ℝ) : ‖Complex.exp (((ξ : ℂ) * Complex.I) * t)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [heq, integral_exp_mul_complex hc, norm_div]
  have hnum : ‖Complex.exp (((ξ : ℂ) * Complex.I) * b) -
      Complex.exp (((ξ : ℂ) * Complex.I) * a)‖ ≤ 2 := by
    simpa only [hn, one_add_one_eq_two] using norm_sub_le
      (Complex.exp (((ξ : ℂ) * Complex.I) * b))
      (Complex.exp (((ξ : ℂ) * Complex.I) * a))
  simpa only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs] using
    div_le_div_of_nonneg_right hnum (norm_nonneg ((ξ : ℂ) * Complex.I))

theorem norm_normalized_integral_exp_mul_I_le {ξ a b : ℝ}
    (hξ : ξ ≠ 0) (hab : a < b) :
    ‖(b - a)⁻¹ • (∫ t in a..b, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I))‖ ≤
      2 / (|ξ| * (b - a)) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sub_pos.mpr hab))]
  calc
    (b - a)⁻¹ * ‖∫ t in a..b, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)‖ ≤
        (b - a)⁻¹ * (2 / |ξ|) :=
      mul_le_mul_of_nonneg_left (norm_integral_exp_mul_I_le hξ a b)
        (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
    _ = 2 / (|ξ| * (b - a)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem norm_normalized_circle_character_le {ξ a b : ℝ}
    (hξ : ξ ≠ 0) (hab : a < b) :
    ‖(b - a)⁻¹ • (∫ t in a..b,
      Complex.exp ((((2 * Real.pi * ξ) * t : ℝ) : ℂ) * Complex.I))‖ ≤
      1 / (Real.pi * |ξ| * (b - a)) := by
  have hfreq : 2 * Real.pi * ξ ≠ 0 := mul_ne_zero (by positivity) hξ
  have h := norm_normalized_integral_exp_mul_I_le hfreq hab
  have ha : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [ha] at h
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem integral_uniform_interval_eq {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ) :
    (∫ t, f t ∂ProbabilityTheory.cond volume (Set.Icc a b)) =
      (b - a)⁻¹ • (∫ t in a..b, f t) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

theorem norm_uniform_interval_circle_character_le {ξ a b : ℝ}
    (hξ : ξ ≠ 0) (hab : a < b) :
    ‖∫ t, Complex.exp ((((2 * Real.pi * ξ) * t : ℝ) : ℂ) * Complex.I)
      ∂ProbabilityTheory.cond volume (Set.Icc a b)‖ ≤
        1 / (Real.pi * |ξ| * (b - a)) := by
  rw [integral_uniform_interval_eq hab.le]
  exact norm_normalized_circle_character_le hξ hab

theorem norm_sampling_interval_character_le {ξ N₀ : ℝ}
    (hξ : ξ ≠ 0) (hN₀ : 0 < N₀) :
    ‖∫ t, Complex.exp ((((2 * Real.pi * ξ) * t : ℝ) : ℂ) * Complex.I)
      ∂ProbabilityTheory.cond volume (Set.Icc (1 / N₀) (2 / N₀))‖ ≤
        N₀ / (Real.pi * |ξ|) := by
  have hab : 1 / N₀ < 2 / N₀ := (div_lt_div_iff_of_pos_right hN₀).2 (by norm_num)
  have h := norm_uniform_interval_circle_character_le hξ hab
  have hlen : 2 / N₀ - 1 / N₀ = 1 / N₀ := by ring
  rw [hlen] at h
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]

theorem norm_sampling_interval_character_le_of_separation {ξ N₀ N m : ℝ}
    (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hm : 0 < m)
    (hsep : N * m ^ 1000 < |ξ|) :
    ‖∫ t, Complex.exp ((((2 * Real.pi * ξ) * t : ℝ) : ℂ) * Complex.I)
      ∂ProbabilityTheory.cond volume (Set.Icc (1 / N₀) (2 / N₀))‖ ≤
        1 / (Real.pi * m ^ 1000) := by
  have hNpos : 0 < N := lt_of_lt_of_le hN₀ hN
  have hξpos : 0 < |ξ| := lt_trans (mul_pos hNpos (pow_pos hm _)) hsep
  have hξ : ξ ≠ 0 := abs_pos.mp hξpos
  calc
    _ ≤ N₀ / (Real.pi * |ξ|) := norm_sampling_interval_character_le hξ hN₀
    _ ≤ N / (Real.pi * |ξ|) :=
      div_le_div_of_nonneg_right hN (mul_nonneg Real.pi_pos.le (abs_nonneg _))
    _ ≤ 1 / (Real.pi * m ^ 1000) := by
      apply (div_le_div_iff₀ (mul_pos Real.pi_pos hξpos)
        (mul_pos Real.pi_pos (pow_pos hm _))).2
      have hh := mul_le_mul_of_nonneg_left hsep.le Real.pi_pos.le
      nlinarith only [hh]

theorem integrable_circle_character (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp ((((2 * Real.pi * ξ) * t : ℝ) : ℂ) * Complex.I)) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun t => (Complex.norm_exp_ofReal_mul_I _).le)

theorem norm_uniform_interval_fourier_sum_sub_zero_le
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ξ : ι → ℝ)
    {a b R : ℝ} (hab : a < b) (hR : 0 < R)
    (hsep : ∀ i ∈ s, ξ i ≠ 0 → R ≤ |ξ i|) :
    ‖(∫ t, ∑ i ∈ s, c i *
        Complex.exp ((((2 * Real.pi * ξ i) * t : ℝ) : ℂ) * Complex.I)
        ∂ProbabilityTheory.cond volume (Set.Icc a b)) -
      ∑ i ∈ s, (if ξ i = 0 then c i else 0)‖ ≤
      (∑ i ∈ s, ‖c i‖) / (Real.pi * R * (b - a)) := by
  classical
  let μ : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc a b)
  let : IsProbabilityMeasure μ := ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (by rw [Real.volume_Icc]; exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne')
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hden : 0 < Real.pi * R * (b - a) :=
    mul_pos (mul_pos Real.pi_pos hR) (sub_pos.mpr hab)
  rw [integral_finsetSum s (fun i _ => (integrable_circle_character μ (ξ i)).const_mul (c i)),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, ‖(∫ t, c i *
          Complex.exp ((((2 * Real.pi * ξ i) * t : ℝ) : ℂ) * Complex.I) ∂μ) -
        (if ξ i = 0 then c i else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖c i‖ / (Real.pi * R * (b - a)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hξ : ξ i = 0
      · simpa [hξ] using div_nonneg (norm_nonneg (c i)) hden.le
      · rw [ite_eq_right hξ, sub_zero, integral_const_mul, norm_mul]
        have ht := norm_uniform_interval_circle_character_le hξ hab
        have hs : 1 / (Real.pi * |ξ i| * (b - a)) ≤
            1 / (Real.pi * R * (b - a)) := by
          apply one_div_le_one_div_of_le hden
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hsep i hi hξ) Real.pi_pos.le) (sub_pos.mpr hab).le
        calc
          _ ≤ ‖c i‖ * (1 / (Real.pi * R * (b - a))) :=
            mul_le_mul_of_nonneg_left (ht.trans hs) (norm_nonneg _)
          _ = _ := by ring
    _ = (∑ i ∈ s, ‖c i‖) / (Real.pi * R * (b - a)) := (Finset.sum_div ..).symm

theorem norm_uniform_interval_fourier_sum_sub_zero_le_card
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ξ : ι → ℝ)
    {a b R C : ℝ} (hab : a < b) (hR : 0 < R)
    (hsep : ∀ i ∈ s, ξ i ≠ 0 → R ≤ |ξ i|) (hc : ∀ i ∈ s, ‖c i‖ ≤ C) :
    ‖(∫ t, ∑ i ∈ s, c i *
        Complex.exp ((((2 * Real.pi * ξ i) * t : ℝ) : ℂ) * Complex.I)
        ∂ProbabilityTheory.cond volume (Set.Icc a b)) -
      ∑ i ∈ s, (if ξ i = 0 then c i else 0)‖ ≤
      (s.card : ℝ) * C / (Real.pi * R * (b - a)) := by
  apply (norm_uniform_interval_fourier_sum_sub_zero_le s c ξ hab hR hsep).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa using Finset.sum_le_sum hc

theorem norm_uniform_interval_two_frequency_sum_le
    (s t : Finset ℤ) (hs : 0 ∈ s) (ht : 0 ∈ t) (c d : ℤ → ℂ)
    {n n' a b R : ℝ} (hab : a < b) (hR : 0 < R)
    (hsep : ∀ i ∈ s, ∀ j ∈ t, (i, j) ≠ (0, 0) →
      R ≤ |(i : ℝ) * n + (j : ℝ) * n'|)
    (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) (hd : ∀ j ∈ t, ‖d j‖ ≤ 1) :
    ‖(∫ u, ∑ i ∈ s, ∑ j ∈ t, (c i * d j) *
        Complex.exp ((((2 * Real.pi * ((i : ℝ) * n + (j : ℝ) * n')) * u : ℝ) : ℂ) *
          Complex.I) ∂ProbabilityTheory.cond volume (Set.Icc a b)) - c 0 * d 0‖ ≤
      ((s.card : ℝ) * (t.card : ℝ)) / (Real.pi * R * (b - a)) := by
  classical
  let ξ : ℤ × ℤ → ℝ := fun p => (p.1 : ℝ) * n + (p.2 : ℝ) * n'
  let e : ℤ × ℤ → ℂ := fun p => c p.1 * d p.2
  have hsep' (p : ℤ × ℤ) (hp : p ∈ s ×ˢ t) (_hpξ : ξ p ≠ 0) : R ≤ |ξ p| := by
    apply hsep p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2
    intro hp0
    apply _hpξ
    have hp0' : p = (0, 0) := hp0
    simp [ξ, hp0']
  have he (p : ℤ × ℤ) (hp : p ∈ s ×ˢ t) : ‖e p‖ ≤ 1 := by
    dsimp [e]
    rw [norm_mul]
    have h1 := hc p.1 (Finset.mem_product.mp hp).1
    have h2 := hd p.2 (Finset.mem_product.mp hp).2
    nlinarith [norm_nonneg (c p.1), norm_nonneg (d p.2)]
  have hzero : (∑ p ∈ s ×ˢ t, (if ξ p = 0 then e p else 0)) = c 0 * d 0 := by
    rw [Finset.sum_eq_single (0, 0)]
    · simp [ξ, e]
    · intro p hp hp0
      have hpos : 0 < |ξ p| := hR.trans_le
        (hsep p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2 hp0)
      rw [ite_eq_right (abs_pos.mp hpos)]
    · intro hnot
      exact (hnot (Finset.mem_product.mpr ⟨hs, ht⟩)).elim
  have h := norm_uniform_interval_fourier_sum_sub_zero_le_card
    (s ×ˢ t) e ξ hab hR hsep' he
  rw [hzero] at h
  simpa only [Finset.sum_product, e, ξ, Finset.card_product, Nat.cast_mul, mul_one] using h

end Invariant233.UniformIntervalFourier

end OAI

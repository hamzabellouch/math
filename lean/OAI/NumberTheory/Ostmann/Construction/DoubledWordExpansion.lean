import OAI.NumberTheory.Ostmann.Construction.PositiveWordStatistic

namespace OAI

/-! # The two independent copies in the original word statistic -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap Classical

theorem weighted_mean_norm_sq {A : Type*} [Fintype A] (w : A → ℝ) (F : A → ℂ) :
    ‖∑ x, (w x : ℂ) * F x‖ ^ 2 =
      ∑ x, ∑ y, w x * w y * (F x * conj (F y)).re := by
  have he : (∑ x, (w x : ℂ) * F x) * conj (∑ x, (w x : ℂ) * F x) =
      ∑ x, ∑ y, ((w x * w y : ℝ) : ℂ) * (F x * conj (F y)) := by
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  rw [Complex.mul_conj'] at he
  have hr := congrArg Complex.re he
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] using hr

noncomputable def jointWordPrior {A : Type*} {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (z : (Fin k → A) × (Fin m → A)) : ℝ := productPrior μ z.1 * productPrior ν z.2

noncomputable def jointWordAmplitude {A B : Type*} {k m : ℕ}
    (F : Fin k → A → ℂ) (R : Fin m → A → ℂ) (bin : (Fin k → A) → B) (b : B)
    (z : (Fin k → A) × (Fin m → A)) : ℂ :=
  if bin z.1 = b then (∏ i, F i (z.1 i)) * ∏ i, R i (z.2 i) else 0

theorem joint_word_mean {A B : Type*} [Fintype A] {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (F : Fin k → A → ℂ) (R : Fin m → A → ℂ) (bin : (Fin k → A) → B) (b : B) :
    (∑ z, (jointWordPrior μ ν z : ℂ) * jointWordAmplitude F R bin b z) =
      binnedWordAverage μ F bin b * ∏ i, ∑ x, (ν i x : ℂ) * R i x := by
  classical
  have hcell : (∑ y : Fin m → A, (productPrior ν y : ℂ) * ∏ i, R i (y i)) =
      ∏ i, ∑ x, (ν i x : ℂ) * R i x := by
    simp_rw [productPrior, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun (i : Fin m) (x : A) => (ν i x : ℂ) * R i x)).symm
  rw [← hcell, binnedWordAverage, Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : bin x = b
  · simp only [jointWordPrior, jointWordAmplitude, h, ite_true, Complex.ofReal_mul]
    ring
  · simp [jointWordPrior, jointWordAmplitude, h]

theorem jointWordAmplitude_norm_le_one {A B : Type*} {k m : ℕ}
    (F : Fin k → A → ℂ) (R : Fin m → A → ℂ) (bin : (Fin k → A) → B) (b : B)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hR : ∀ i x, ‖R i x‖ ≤ 1)
    (z : (Fin k → A) × (Fin m → A)) :
    ‖jointWordAmplitude F R bin b z‖ ≤ 1 := by
  unfold jointWordAmplitude
  split_ifs
  · rw [norm_mul, norm_prod, norm_prod]
    have hf := Finset.prod_le_one₀ (s := Finset.univ) (fun i _ => norm_nonneg (F i (z.1 i)))
      (fun i _ => hF i (z.1 i))
    have hr := Finset.prod_le_one₀ (s := Finset.univ) (fun i _ => norm_nonneg (R i (z.2 i)))
      (fun i _ => hR i (z.2 i))
    exact (mul_le_mul_of_nonneg_left hr (Finset.prod_nonneg (fun i _ => norm_nonneg _))).trans
      (by simpa only [mul_one] using hf)
  · simp

theorem bounded_schwartz_real_correlation_summable (ψ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (hX : 0 < X) (F G : ℤ → ℂ) (hF : ∀ a, ‖F a‖ ≤ 1) (hG : ∀ a, ‖G a‖ ≤ 1) :
    Summable (fun a : ℤ => (ψ ((a : ℝ) / X)).re * (F a * conj (G a)).re) := by
  have hs : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded hs
  intro a
  rw [Real.norm_eq_abs, abs_mul]
  have hc : |(F a * conj (G a)).re| ≤ 1 := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left (hG a) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hF a)
  exact (mul_le_mul_of_nonneg_left hc (abs_nonneg _)).trans
    (by simpa only [mul_one] using Complex.abs_re_le_norm (ψ ((a : ℝ) / X)))

/-- Each role is sampled twice under its original law. Bin restrictions are
indicators in the amplitude; the prior is never renormalized. -/
theorem word_statistic_double_expansion {A B : Type*} [Fintype A] {k m : ℕ}
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (F : ℤ → Fin k → A → ℂ) (R : ℤ → Fin m → A → ℂ)
    (bin : (Fin k → A) → B) (b : B) (a : ℤ) :
    wordStatisticTerm ψ X (fun a => binnedWordAverage μ (F a) bin b)
      (fun i a => ∑ x, (ν i x : ℂ) * R a i x) a =
      (ψ ((a : ℝ) / X)).re *
        ∑ z, ∑ z', jointWordPrior μ ν z * jointWordPrior μ ν z' *
          (jointWordAmplitude (F a) (R a) bin b z *
            conj (jointWordAmplitude (F a) (R a) bin b z')).re := by
  calc
    _ = (ψ ((a : ℝ) / X)).re *
        ‖binnedWordAverage μ (F a) bin b * ∏ i, ∑ x, (ν i x : ℂ) * R a i x‖ ^ 2 := by
      simp only [wordStatisticTerm, norm_mul, norm_prod, mul_pow, Finset.prod_pow]
      ring
    _ = (ψ ((a : ℝ) / X)).re *
        ‖∑ z, (jointWordPrior μ ν z : ℂ) * jointWordAmplitude (F a) (R a) bin b z‖ ^ 2 := by
      rw [joint_word_mean]
    _ = _ := congrArg (fun t => (ψ ((a : ℝ) / X)).re * t)
      (weighted_mean_norm_sq (jointWordPrior μ ν) (jointWordAmplitude (F a) (R a) bin b))

/-- The finite original prime averages commute with the physical Schwartz sum.
No conditioning or change of prior occurs in this expansion. -/
theorem word_statistic_tsum_double_expansion {A B : Type*} [Fintype A] {k m : ℕ}
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (F : ℤ → Fin k → A → ℂ) (R : ℤ → Fin m → A → ℂ)
    (hF : ∀ a i x, ‖F a i x‖ ≤ 1) (hR : ∀ a i x, ‖R a i x‖ ≤ 1)
    (bin : (Fin k → A) → B) (b : B) :
    (∑' a : ℤ, wordStatisticTerm ψ X (fun a => binnedWordAverage μ (F a) bin b)
      (fun i a => ∑ x, (ν i x : ℂ) * R a i x) a) =
      ∑ z, ∑ z', jointWordPrior μ ν z * jointWordPrior μ ν z' *
        ∑' a : ℤ, (ψ ((a : ℝ) / X)).re *
          (jointWordAmplitude (F a) (R a) bin b z *
            conj (jointWordAmplitude (F a) (R a) bin b z')).re := by
  let C (a : ℤ) (z z' : (Fin k → A) × (Fin m → A)) : ℝ :=
    (ψ ((a : ℝ) / X)).re * (jointWordAmplitude (F a) (R a) bin b z *
      conj (jointWordAmplitude (F a) (R a) bin b z')).re
  have hC (z z' : (Fin k → A) × (Fin m → A)) : Summable (fun a => C a z z') :=
    bounded_schwartz_real_correlation_summable ψ X hX _ _
      (fun a => jointWordAmplitude_norm_le_one (F a) (R a) bin b (hF a) (hR a) z)
      (fun a => jointWordAmplitude_norm_le_one (F a) (R a) bin b (hF a) (hR a) z')
  have hs (z z') : Summable (fun a => jointWordPrior μ ν z * jointWordPrior μ ν z' * C a z z') :=
    (hC z z').mul_left _
  have he (a : ℤ) : wordStatisticTerm ψ X (fun a => binnedWordAverage μ (F a) bin b)
      (fun i a => ∑ x, (ν i x : ℂ) * R a i x) a =
      ∑ z, ∑ z', jointWordPrior μ ν z * jointWordPrior μ ν z' * C a z z' := by
    rw [word_statistic_double_expansion]
    simp only [Finset.mul_sum, C]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro z' _
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun z _ => summable_sum (fun z' _ => hs z z'))]
  apply Finset.sum_congr rfl
  intro z _
  rw [Summable.tsum_finsetSum (fun z' _ => hs z z')]
  simp only [tsum_mul_left, C]

end Ostmann

end OAI

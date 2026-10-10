import OAI.NumberTheory.Ostmann.Supply.LocalSparseKernelContraction

namespace OAI

/-! # Scalar control on the polydisc used for kernel truncation -/

namespace Ostmann
open scoped Classical BigOperators

theorem residueKernelScalar_sparse_norm_le {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖residueKernelScalar S (sparseAdditiveKernel E t)‖ ≤ t / p := by
  let a := residueKernelScalar S (sparseAdditiveKernel E t)
  have hreal : a = (a.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im, a] using residueKernelScalar_sparse_real S E hS hSp hE t
  have hlo := residueKernelScalar_sparse_lower S E hS hSp hE t ht
  have hhi := residueKernelScalar_sparse_re_le S E hS hSp hE t 1 ht (by norm_num; positivity)
  have hhi' : a.re ≤ 0 := by simpa only [one_pow, sub_self, mul_zero, neg_zero, zero_div] using hhi
  change ‖a‖ ≤ _
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hhi']
  change -t / p ≤ a.re at hlo
  simpa only [neg_div, neg_neg] using neg_le_neg hlo

theorem polydisc_scalar_error_bound (p ε : ℝ) (a b c d : ℂ) (hp : 0 < p)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (ha : ‖a‖ ≤ (17 / 20) / p) (hb : ‖b‖ ≤ (289 / 100) * ε / p)
    (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000) :
    ‖c * a + d * b‖ ≤ 2 / p := by
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  apply (add_le_add (mul_le_mul hc ha (norm_nonneg _) (by norm_num))
    (mul_le_mul hd hb (norm_nonneg _) (by norm_num))).trans
  apply (le_div_iff₀ hp).mpr
  have he : ((103 / 50) * ((17 / 20) / p) +
      (10609 / 10000) * ((289 / 100) * ε / p)) * p =
      (103 / 50) * (17 / 20) + (10609 / 10000) * ((289 / 100) * ε) := by
    field_simp
  rw [he]
  linarith

theorem polydisc_scalar_norm_bounds (p ε : ℝ) (a b c d : ℂ) (hp : 100 ≤ p)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (ha : ‖a‖ ≤ (17 / 20) / p) (hb : ‖b‖ ≤ (289 / 100) * ε / p)
    (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000) :
    (19 / 20 : ℝ) ≤ ‖1 + c * a + d * b‖ ∧ ‖1 + c * a + d * b‖ ≤ 1 + 2 / p := by
  have hp0 : 0 < p := by linarith
  have he := polydisc_scalar_error_bound p ε a b c d hp0 hε hεsmall ha hb hc hd
  have hrewrite : 1 + c * a + d * b = 1 + (c * a + d * b) := by ring
  rw [hrewrite]
  constructor
  · have hh := norm_add_le (1 + (c * a + d * b)) (-(c * a + d * b))
    simp only [add_neg_cancel_right, norm_one, norm_neg] at hh
    have hpbound : 2 / p ≤ (1 / 20 : ℝ) := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  · exact (norm_add_le _ _).trans (by simpa only [norm_one] using add_le_add le_rfl he)

end Ostmann

end OAI

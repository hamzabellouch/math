import OAI.NumberTheory.JointDickman.Counting.WeightedCoefficientLaw
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! # Complex smooth tests of the actual coefficient progression law -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

private theorem density_log_continuousOn (c : ℕ → ℝ) (H B : ℕ)
    (hB : 0 < B) {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t => coefficientDensity c H B (Real.log t / B)) (Set.Icc a b) := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have heq : (fun t => coefficientDensity c H B (Real.log t / B)) =
      fun t => coefficientScale B * roughDensityPolynomial c
        (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) H (Real.log t) := by
    funext t
    simp only [coefficientDensity, mul_div_cancel₀ _ hB0]
  rw [heq]
  intro t ht
  exact (continuousAt_const.mul ((roughDensityPolynomial_continuousAt c _ _ H
    (Real.log_pos (ha.trans_le ht.1))).comp
      (Real.continuousAt_log (by linarith [ht.1] : t ≠ 0)))).continuousWithinAt

open Classical in
/-- The same fixed expansion works for all complex C¹ tests; only two real
component estimates are used. -/
theorem coefficientProgression_complex_test
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b : ℝ, 9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) → ∀ r : (ZMod q)ˣ,
      ∀ φ φ' : ℝ → ℂ, ∀ M N : ℝ, 0 ≤ M → 0 ≤ N →
      (∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ M) → (∀ t ∈ Set.Icc a b, ‖φ' t‖ ≤ N) →
      ‖(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)‖ ≤
        K * (B : ℝ) ^ (-D) * b * (2 * M + N * (b - a)) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := coefficientProgression_smooth_test hSD hSW hM hD
  refine ⟨c, hc, hcpos, H, 2 * K, by positivity, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hboundB hB
  intro a b ha hab hloga q _ hq r φ φ' M N hM0 hN hφ hφ' hvalue hderiv
  have hre := hboundB a b ha hab hloga q hq r (fun t => (φ t).re)
    (fun t => (φ' t).re) M N hM0 hN
    (fun t ht => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hφ t ht))
    (Complex.continuous_re.comp_continuousOn hφ')
    (fun t ht => (Complex.abs_re_le_norm _).trans (hvalue t ht))
    (fun t ht => (Complex.abs_re_le_norm _).trans (hderiv t ht))
  have him := hboundB a b ha hab hloga q hq r (fun t => (φ t).im)
    (fun t => (φ' t).im) M N hM0 hN
    (fun t ht => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hφ t ht))
    (Complex.continuous_im.comp_continuousOn hφ')
    (fun t ht => (Complex.abs_im_le_norm _).trans (hvalue t ht))
    (fun t ht => (Complex.abs_im_le_norm _).trans (hderiv t ht))
  have hcont : ContinuousOn φ (Set.Icc a b) :=
    fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun t => φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) volume a b :=
    (hcont.mul (Complex.continuous_ofReal.comp_continuousOn
      (density_log_continuousOn c H B hB (by linarith)))).intervalIntegrable_of_Icc hab
  have hrint := intervalIntegral.intervalIntegral_re hint
  have hiint := intervalIntegral.intervalIntegral_im hint
  change (∫ t in a..b, (φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)).re) =
    (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)).re at hrint
  change (∫ t in a..b, (φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)).im) =
    (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)).im at hiint
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add] at hrint hiint
  have hreq : ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)).re =
      (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          (φ n).re * coefficientWeight B n else 0) -
        (∫ t in a..b, (φ t).re * coefficientDensity c H B (Real.log t / B)) / q.totient := by
    simp only [Complex.sub_re, ← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.re_sum, apply_ite Complex.re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      mul_zero, sub_zero, ← hrint]
  have hieq : ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)).im =
      (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          (φ n).im * coefficientWeight B n else 0) -
        (∫ t in a..b, (φ t).im * coefficientDensity c H B (Real.log t / B)) / q.totient := by
    simp only [Complex.sub_im, ← Complex.ofReal_natCast, Complex.div_ofReal_im, Complex.im_sum, apply_ite Complex.im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im,
      mul_zero, zero_add, ← hiint]
  calc
    _ ≤ |((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)).re| +
        |((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by rw [hreq, hieq]; nlinarith [hre, him]

end JointDickman

end OAI

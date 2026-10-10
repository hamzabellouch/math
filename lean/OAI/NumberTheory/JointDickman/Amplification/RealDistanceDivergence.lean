import OAI.NumberTheory.JointDickman.Arithmetic.PrimePhaseDivergence

namespace OAI

/-! # Uniform distance separation for bounded real coefficients -/
namespace JointDickman
open Complex Filter Finset PublishedInputs
open scoped Topology

lemma real_primeDistance_lower (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hreal : ∀ n, (f n).im = 0) (X t : ℝ) :
    (∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
      (1 - |Real.cos (t * Real.log (p : ℝ))|) / (p : ℝ)) ≤
        primeDistanceSquared f X t := by
  unfold primeDistanceSquared
  apply sum_le_sum
  intro p _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
  have habs : |(f p).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (hf p)
  have hmul : (f p).re * Real.cos (t * Real.log (p : ℝ)) ≤
      |Real.cos (t * Real.log (p : ℝ))| := by
    calc
      _ ≤ |(f p).re * Real.cos (t * Real.log (p : ℝ))| := le_abs_self _
      _ = |(f p).re| * |Real.cos (t * Real.log (p : ℝ))| := abs_mul _ _
      _ ≤ 1 * |Real.cos (t * Real.log (p : ℝ))| :=
        mul_le_mul_of_nonneg_right habs (abs_nonneg _)
      _ = _ := one_mul _
  have he : (f p * Complex.exp (-((t * Real.log (p : ℝ) : ℝ) : ℂ)*I)).re =
      (f p).re * Real.cos (t * Real.log (p : ℝ)) := by
    simp only [Complex.mul_re, hreal, zero_mul, sub_zero, Complex.exp_re,
      Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      neg_zero, add_zero, Real.exp_zero, one_mul, Real.cos_neg]
  rw [he]
  linarith

/-- The bound is uniform in the real coefficients, including scale-dependent
bin interpolants. Multiplicativity is not needed for this distance bound. -/
theorem real_primeDistance_diverges (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (f : ArithmeticFunction ℂ),
      (∀ n, ‖f n‖ ≤ 1) → (∀ n, (f n).im = 0) →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ X → R ≤ primeDistanceSquared f X t := by
  filter_upwards [prime_abs_cosine_defect_diverges R] with X hX
  intro f hf hreal t htlo ht
  have hb := hX (2*t) (by rw [abs_mul]; norm_num; linarith)
    (by rw [abs_mul]; norm_num; linarith)
  have he : (∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
      (1 - |Real.cos ((2*t) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) =
      ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
        (1 - |Real.cos (t * Real.log (p : ℝ))|) / (p : ℝ) := by
    apply sum_congr rfl
    intro p _
    rw [show (2*t) * Real.log (p : ℝ) / 2 = t * Real.log (p : ℝ) by ring]
  rw [he] at hb
  exact hb.trans (real_primeDistance_lower f hf hreal X t)

end JointDickman

end OAI

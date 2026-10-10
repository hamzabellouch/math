import OAI.NumberTheory.JointDickman.Arithmetic.PrimePhaseDivergence

namespace OAI

/-! # Qualitative separation of two pretentious twists -/
namespace JointDickman
open Complex Finset Filter PublishedInputs
open scoped Topology

lemma phase_sum_norm (n : ℕ) (t s : ℝ) :
    ‖Complex.exp (-((t * Real.log (n : ℝ) : ℝ) : ℂ) * I) +
      Complex.exp (-((s * Real.log (n : ℝ) : ℝ) : ℂ) * I)‖ =
      2 * |Real.cos ((t-s) * Real.log (n : ℝ) / 2)| := by
  let u := -(t+s) / 2
  let v := -(t-s) * Real.log (n : ℝ) / 2
  have he : Complex.exp (-((t * Real.log (n : ℝ) : ℝ) : ℂ) * I) +
      Complex.exp (-((s * Real.log (n : ℝ) : ℝ) : ℂ) * I) =
      Complex.exp (((u * Real.log (n : ℝ) : ℝ) : ℂ) * I) * ((2 : ℂ) * (Real.cos v : ℂ)) := by
    rw [Complex.ofReal_cos, Complex.two_cos, mul_add, ←Complex.exp_add, ←Complex.exp_add]
    congr 1 <;> congr 1 <;> dsimp [u, v] <;> push_cast <;> ring
  rw [he, norm_mul, Complex.norm_exp]
  have hr : ((((u * Real.log (n : ℝ) : ℝ) : ℂ) * I)).re = 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self]
  rw [hr, Real.exp_zero, one_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs]
  have hv : v = -((t-s) * Real.log (n : ℝ) / 2) := by dsimp [v]; ring
  rw [hv, Real.cos_neg]

lemma two_twist_distance_lower (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (X t s : ℝ) :
    2 * (∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
      (1 - |Real.cos ((t-s) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
      primeDistanceSquared f X t + primeDistanceSquared f X s := by
  unfold primeDistanceSquared
  rw [mul_sum, ←sum_add_distrib]
  apply sum_le_sum
  intro p _
  rw [←add_div, ←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
  have hre : (f p * Complex.exp (-((t * Real.log (p : ℝ) : ℝ) : ℂ)*I)).re +
      (f p * Complex.exp (-((s * Real.log (p : ℝ) : ℝ) : ℂ)*I)).re ≤
      ‖Complex.exp (-((t * Real.log (p : ℝ) : ℝ) : ℂ)*I) +
        Complex.exp (-((s * Real.log (p : ℝ) : ℝ) : ℂ)*I)‖ := by
    calc
      _ = (f p * (Complex.exp (-((t * Real.log (p : ℝ) : ℝ) : ℂ)*I) +
          Complex.exp (-((s * Real.log (p : ℝ) : ℝ) : ℂ)*I))).re := by
        rw [mul_add, add_re]
      _ ≤ _ := (Complex.re_le_norm _).trans (by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hf p))
  rw [phase_sum_norm] at hre
  linarith

/-- For any desired distance, two bounded-frequency twists separated by at
least one cannot both stay close to the same bounded multiplicative data.
The bound is uniform in the coefficient function. -/
theorem two_twist_distance_diverges (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (f : ArithmeticFunction ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ t s : ℝ, |t| ≤ X → |s| ≤ X → 1 ≤ |t-s| →
        2*R ≤ primeDistanceSquared f X t + primeDistanceSquared f X s := by
  filter_upwards [prime_abs_cosine_defect_diverges R] with X hX
  intro f hf t s ht hs hsep
  have hts : |t-s| ≤ 2*X := (abs_sub t s).trans (by linarith)
  have hbound := hX (t-s) hsep hts
  have hdist := two_twist_distance_lower f hf X t s
  linarith

end JointDickman

end OAI

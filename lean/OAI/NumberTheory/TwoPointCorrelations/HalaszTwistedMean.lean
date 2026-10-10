import OAI.NumberTheory.TwoPointCorrelations.HalaszMeanValue

namespace OAI

/-! Height translation for the ordinary mean estimate. This is the
form applied to Dirichlet polynomials on a vertical line. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped ComplexConjugate

lemma halasz_twist_add (t u : ℝ) (n : ℕ) :
    mrtArchimedeanTwist (t + u) n = mrtArchimedeanTwist t n * mrtArchimedeanTwist u n := by
  simp only [mrtArchimedeanTwist, add_mul, Complex.ofReal_add, Complex.exp_add]

lemma halasz_twist_mul (t : ℝ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    mrtArchimedeanTwist t (a * b) = mrtArchimedeanTwist t a * mrtArchimedeanTwist t b := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [mrtArchimedeanTwist, Nat.cast_mul, Real.log_mul har.ne' hbr.ne',
    mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

noncomputable def halaszTwistedFunction (f : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  f n * conj (mrtArchimedeanTwist t n)

lemma halasz_twisted_one (f : ℕ → ℂ) (hf : f 1 = 1) (t : ℝ) :
    halaszTwistedFunction f t 1 = 1 := by simp [halaszTwistedFunction, mrtArchimedeanTwist, hf]

lemma halasz_twisted_mul (f : ℕ → ℂ)
    (hf : ∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b)
    (t : ℝ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    halaszTwistedFunction f t (a * b) = halaszTwistedFunction f t a * halaszTwistedFunction f t b := by
  simp only [halaszTwistedFunction, hf a b ha hb, halasz_twist_mul t ha hb, map_mul]
  ring

lemma halasz_twisted_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) (t : ℝ) :
    OneBounded (halaszTwistedFunction f t) := by
  intro n hn
  simpa only [halaszTwistedFunction, norm_mul, norm_conj, mrtArchimedeanTwist_norm, mul_one]
    using hf n hn

lemma halasz_twisted_distance (f : ℕ → ℂ) (t u : ℝ) (N : ℕ) :
    squaredDistance (halaszTwistedFunction f t) (mrtArchimedeanTwist u) N =
      squaredDistance f (mrtArchimedeanTwist (t + u)) N := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p _
  simp only [halaszTwistedFunction, halasz_twist_add, map_mul, mul_assoc]

theorem halasz_twisted_mean_value : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b) → OneBounded f →
    ∀ (t T M : ℝ), 0 ≤ M → |t| + Real.log (N : ℝ) ^ 8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → M ≤ squaredDistance f (mrtArchimedeanTwist v) N) →
      ‖∑ n ∈ Icc 1 N, f n * conj (mrtArchimedeanTwist t n)‖ ≤ C * N *
        ((M + 1) * Real.exp (-M) + Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C, X₀, hC, hmean⟩ := halasz_mean_value
  refine ⟨C, X₀, hC, ?_⟩
  intro N hXN f hf1 hf hbound t T M hM hT hd
  apply hmean N hXN (halaszTwistedFunction f t) (halasz_twisted_one f hf1 t)
    (halasz_twisted_mul f hf t) (halasz_twisted_oneBounded f hbound t) M hM
  intro u hu
  rw [halasz_twisted_distance]
  apply hd
  exact (abs_add_le t u).trans ((add_le_add le_rfl (abs_le.mpr hu)).trans hT)

end TwoPointCorrelations

end OAI

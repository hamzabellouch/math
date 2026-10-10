import OAI.NumberTheory.TwoPointCorrelations.HalaszGeneralMean
import OAI.NumberTheory.TwoPointCorrelations.HalaszTwistedMean

namespace OAI

/-! General multiplicative ordinary means after a height translation. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped ComplexConjugate

lemma halasz_twisted_multiplicative (f : ℕ → ℂ) (hf : Multiplicative f) (t : ℝ) :
    Multiplicative (halaszTwistedFunction f t) := by
  intro a b ha hb hab
  simp only [halaszTwistedFunction, hf a b ha hb hab, halasz_twist_mul t ha hb, map_mul]
  ring

theorem halasz_general_twisted_mean : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (f : ℕ → ℂ), f 1 = 1 → Multiplicative f → OneBounded f →
    ∀ (t T M : ℝ), 0 ≤ M → |t| + Real.log (N : ℝ) ^ 8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → M ≤ squaredDistance f (mrtArchimedeanTwist v) N) →
      ‖∑ n ∈ Icc 1 N, f n * conj (mrtArchimedeanTwist t n)‖ ≤ C * N *
        ((M + 1) * Real.exp (-M) + Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C, X₀, hC, hmean⟩ := halasz_general_mean_value
  refine ⟨C, X₀, hC, ?_⟩
  intro N hXN f hf1 hf hbound t T M hM hT hd
  apply hmean N hXN (halaszTwistedFunction f t) (halasz_twisted_one f hf1 t)
    (halasz_twisted_multiplicative f hf t) (halasz_twisted_oneBounded f hbound t) M hM
  intro u hu
  rw [halasz_twisted_distance]
  apply hd
  exact (abs_add_le t u).trans ((add_le_add le_rfl (abs_le.mpr hu)).trans hT)

end TwoPointCorrelations

end OAI

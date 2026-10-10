import OAI.NumberTheory.Ostmann.Construction.SmoothGiantActiveSupport

namespace OAI

/-! # Removing zero-weight giant labels preserves the full original law -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothGiantLivePrimes (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) : Finset ℕ :=
  P.filter (fun p => φ (Real.log p - G) ≠ 0)

theorem smoothGiantLivePrimes_subset (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) :
    smoothGiantLivePrimes P φ G ⊆ P := Finset.filter_subset _ _

theorem smoothGiantMass_live (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) :
    smoothGiantMass (smoothGiantLivePrimes P φ G) φ G = smoothGiantMass P φ G := by
  unfold smoothGiantMass smoothGiantLivePrimes
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : φ (Real.log p - G) = 0 <;> simp only [h, ne_eq, not_true_eq_false,
    ite_false, zero_div, not_false_eq_true, ite_true]

theorem smoothGiantPrior_live_nonzero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (p : smoothGiantLivePrimes P φ G) :
    smoothGiantPrior (smoothGiantLivePrimes P φ G) φ G p ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (Real.exp_ne_zero _) (Finset.mem_filter.mp p.property).2
  · exact_mod_cast (hP _ (smoothGiantLivePrimes_subset P φ G p.property)).ne_zero

theorem smoothGiantLivePrimes_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : smoothGiantLivePrimes P φ G) :
    Real.exp (G - 1) < (p : ℝ) ∧ (p : ℝ) < Real.exp (G + 1) :=
  smoothGiantPrior_active_bounds _ (fun q hq => hP q (smoothGiantLivePrimes_subset P φ G hq))
    φ G hout p (smoothGiantPrior_live_nonzero P hP φ G p)

theorem smoothGiantPrior_sum_live (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) (f : ℕ → ℂ) :
    (∑ p : P, (smoothGiantPrior P φ G p : ℂ) * f p) =
      ∑ p : smoothGiantLivePrimes P φ G,
        (smoothGiantPrior (smoothGiantLivePrimes P φ G) φ G p : ℂ) * f p := by
  have hh (Q : Finset ℕ) :
      (∑ p : Q, (smoothGiantPrior Q φ G p : ℂ) * f p) =
        ∑ p ∈ Q, ((Real.exp (smoothGiantLogNormalizer Q φ G) * φ (Real.log p - G) /
          (p : ℝ) : ℝ) : ℂ) * f p := by
    exact Finset.sum_coe_sort Q (fun p : ℕ =>
      ((Real.exp (smoothGiantLogNormalizer Q φ G) * φ (Real.log p - G) /
        (p : ℝ) : ℝ) : ℂ) * f p)
  rw [hh P, hh (smoothGiantLivePrimes P φ G)]
  simp only [smoothGiantLogNormalizer, smoothGiantMass_live]
  symm
  unfold smoothGiantLivePrimes
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : φ (Real.log p - G) = 0 <;> simp [h]

theorem smoothGiantPrior_double_sum_live (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (f : ℕ → ℕ → ℂ) :
    (∑ x : P, (smoothGiantPrior P φ G x : ℂ) *
      ∑ y : P, (smoothGiantPrior P φ G y : ℂ) * f x y) =
    ∑ x : smoothGiantLivePrimes P φ G,
      (smoothGiantPrior (smoothGiantLivePrimes P φ G) φ G x : ℂ) *
      ∑ y : smoothGiantLivePrimes P φ G,
        (smoothGiantPrior (smoothGiantLivePrimes P φ G) φ G y : ℂ) * f x y := by
  rw [smoothGiantPrior_sum_live P φ G
    (fun x => ∑ y : P, (smoothGiantPrior P φ G y : ℂ) * f x y)]
  apply Finset.sum_congr rfl
  intro x _
  rw [smoothGiantPrior_sum_live P φ G (f x)]

end Ostmann

end OAI

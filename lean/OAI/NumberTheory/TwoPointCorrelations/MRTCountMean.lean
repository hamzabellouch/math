import OAI.NumberTheory.TwoPointCorrelations.MRTCountMask
import OAI.NumberTheory.TwoPointCorrelations.HalaszGeneralTwist

namespace OAI

/-! Ordinary mean cancellation with the literal reciprocal prime-count
weight. Integrating multiplicative soft masks gives the cofactor weight
exactly, while the missing-band and count masks lose only one factor two
in pretentious distance. -/

namespace TwoPointCorrelations

open Finset
open scoped ComplexConjugate Classical

noncomputable def mrtMissingCoefficient (F : ℕ → ℂ) (Q : Finset ℕ)
    (n : ℕ) : ℂ := F n * (mrtPrimeMask Q n : ℂ)

lemma mrtMissingCoefficient_one (F : ℕ → ℂ) (hF : F 1 = 1)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    mrtMissingCoefficient F Q 1 = 1 := by
  simp only [mrtMissingCoefficient, hF, mrtPrimeMask_one Q hQ, Complex.ofReal_one, mul_one]

lemma mrtMissingCoefficient_multiplicative (F : ℕ → ℂ) (hF : Multiplicative F)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    Multiplicative (mrtMissingCoefficient F Q) := by
  intro m n hm hn hcop
  simp only [mrtMissingCoefficient, hF m n hm hn hcop,
    mrtPrimeMask_mul Q hQ, Complex.ofReal_mul]
  ring

lemma mrtMissingCoefficient_oneBounded (F : ℕ → ℂ) (hF : OneBounded F)
    (Q : Finset ℕ) : OneBounded (mrtMissingCoefficient F Q) := by
  intro n hn
  rw [mrtMissingCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mrtPrimeMask_bounds Q n).1]
  exact (mul_le_mul (hF n hn) (mrtPrimeMask_bounds Q n).2
    (mrtPrimeMask_bounds Q n).1 zero_le_one).trans_eq (mul_one 1)

lemma mrt_missing_count_one (F : ℕ → ℂ) (hF : F 1 = 1)
    (Q P : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime) (u : ℝ) :
    mrtCountMaskedCoefficient (mrtMissingCoefficient F Q) P u 1 = 1 := by
  simp only [mrtCountMaskedCoefficient, mrtMissingCoefficient_one F hF Q hQ,
    mrtCountMask_one P hP, Complex.ofReal_one, mul_one]

/-- The constant is uniform over both finite prime masks and the entire
softening parameter. No lower bound on the number of selected primes is
required. -/
theorem mrt_missing_count_prefix_mean : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ (Q P : Finset ℕ), (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    ∀ (t T M : ℝ), 0 ≤ M → |t| + Real.log (N : ℝ) ^ 8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → 2 * M ≤ squaredDistance F (mrtArchimedeanTwist v) N) →
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖∑ n ∈ Icc 1 N,
          mrtCountMaskedCoefficient (mrtMissingCoefficient F Q) P u n *
            conj (mrtArchimedeanTwist t n)‖ ≤ C * N *
          ((M + 1) * Real.exp (-M) + Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C, X₀, hC, hmean⟩ := halasz_general_twisted_mean
  refine ⟨C, X₀, hC, ?_⟩
  intro N hN F hF1 hFm hFb Q P hQ hP t T M hM hT hd u hu hu1
  apply hmean N hN _ (mrt_missing_count_one F hF1 Q P hQ hP u)
    ((mrtMissingCoefficient_multiplicative F hFm Q hQ).mrtCountMaskedCoefficient P hP u)
    ((mrtMissingCoefficient_oneBounded F hFb Q).mrtCountMaskedCoefficient P hu hu1)
    t T M hM hT
  intro v hv
  have hm := mrt_missing_count_mask_distance F (mrtArchimedeanTwist v) Q P hu hu1 N
    (fun p hp => hFb p ((mem_filter.mp hp).2.pos))
    (fun p _ => by rw [mrtArchimedeanTwist_norm])
  change squaredDistance F (mrtArchimedeanTwist v) N ≤
    2 * squaredDistance
      (mrtCountMaskedCoefficient (mrtMissingCoefficient F Q) P u)
      (mrtArchimedeanTwist v) N at hm
  linarith [hd v hv]

/-- The reciprocal-count weighted cofactor prefix is the integral of the
preceding multiplicative means, not an additional analytic hypothesis. -/
theorem mrt_reciprocal_count_prefix_mean : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ (Q P : Finset ℕ), (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    ∀ (t T M : ℝ), 0 ≤ M → |t| + Real.log (N : ℝ) ^ 8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → 2 * M ≤ squaredDistance F (mrtArchimedeanTwist v) N) →
      ‖∑ n ∈ Icc 1 N,
        (mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n)) /
          ((finitePrimeDivisorCount P n : ℂ) + 1)‖ ≤ C * N *
        ((M + 1) * Real.exp (-M) + Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C, X₀, hC, hmean⟩ := mrt_missing_count_prefix_mean
  refine ⟨C, X₀, hC, ?_⟩
  intro N hN F hF1 hFm hFb Q P hQ hP t T M hM hT hd
  apply mrt_reciprocal_count_polynomial_bound (Icc 1 N) P
    (fun n => mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n))
  intro u hu hu1
  have hm := hmean N hN F hF1 hFm hFb Q P hQ hP t T M hM hT hd u hu hu1
  convert hm using 1
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [mrtCountMaskedCoefficient]
  ring

end TwoPointCorrelations

end OAI

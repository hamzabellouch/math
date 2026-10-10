import OAI.NumberTheory.TwoPointCorrelations.HalaszGeneralMean
import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceInput

namespace OAI

/-! # The general Halász estimate with the joint-law prime distance -/
namespace JointDickman
open Complex Finset PublishedInputs
open scoped ComplexConjugate

lemma halasz_distance_eq (f : ArithmeticFunction ℂ) (N : ℕ) (t : ℝ) :
    TwoPointCorrelations.squaredDistance f (TwoPointCorrelations.mrtArchimedeanTwist t) N =
      primeDistanceSquared f N t := by
  have hS : TwoPointCorrelations.primesUpTo N = (Icc 2 N).filter Nat.Prime := by
    ext p
    simp only [TwoPointCorrelations.primesUpTo, mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨hp, hprime⟩
      exact ⟨⟨hprime.two_le, by omega⟩, hprime⟩
    · rintro ⟨⟨_, hp⟩, hprime⟩
      exact ⟨by omega, hprime⟩
  unfold TwoPointCorrelations.squaredDistance primeDistanceSquared
  rw [hS, Nat.floor_natCast]
  apply sum_congr rfl
  intro p _
  unfold TwoPointCorrelations.mrtArchimedeanTwist
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [neg_mul]

/-- The logarithmic-height mean bound for normalized ordinary multiplicative
functions, with the exact prime-distance convention used in this result. -/
theorem halasz_arithmetic_mean_value : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ N : ℕ, X₀ ≤ N → ∀ f : ArithmeticFunction ℂ,
      f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) → ∀ M : ℝ, 0 ≤ M →
      (∀ t : ℝ, |t| ≤ Real.log (N : ℝ)^8 → M ≤ primeDistanceSquared f N t) →
      ‖∑ n ∈ Icc 1 N, f n‖ ≤ C*N*
        ((M+1)*Real.exp (-M) + Real.log (Real.log N)/Real.log N) := by
  obtain ⟨C, X₀, hC, hbound⟩ := TwoPointCorrelations.halasz_general_mean_value
  refine ⟨C, X₀, hC, ?_⟩
  intro N hN f hf hnorm M hM hdist
  apply hbound N hN f hf.1 (fun m n _ _ hmn => hf.2 hmn)
    (fun n _ => hnorm n) M hM
  intro t ht
  rw [halasz_distance_eq]
  exact hdist t (abs_le.mpr ht)

end JointDickman

end OAI

import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstSecondMain
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticTransformedComparison
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOffDiagonalBound

namespace OAI

/-! # The actual two transformed main terms, summed over the original pairs -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticSmallPairMain (M D q K : ℕ) : ℂ :=
  ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
    (quadraticSmallScale M b : ℂ) * (((2 * (q * D)).totient : ℂ) / (2 * (q * D) : ℕ)) *
      (∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (jacobiSym b q : ℂ)

noncomputable def quadraticPairMainDifference (M D q K : ℕ) : ℂ :=
  quadraticFirstSecondMainKernel M D q K - quadraticSmallPairMain M D q K

theorem quadratic_small_pair_core_main (M D q K : ℕ) (J : ℝ) :
    quadraticSmallPairCore M K D q J = quadraticSmallPairMain M D q K +
      ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
        (jacobiSym b q : ℂ) * quadraticSmallPairCorrection M J (2 * (q * D)) b := by
  unfold quadraticSmallPairCore quadraticSmallPairMain
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [quadratic_small_pair_core]
  ring

theorem quadratic_pair_main_difference_sum (M N D K : ℕ) (v : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D,
      v z.1 * conj (v z.2) * quadraticPairMainDifference M D (quadraticPairKernel z.1 z.2) K) =
      quadraticTransformedFirstMain M N D K quadraticSieveWeight v -
        quadraticSmallTransformedMain M N D K quadraticSieveWeight v := by
  unfold quadraticPairMainDifference
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp_rw [quadratic_first_second_main_kernel]
    unfold quadraticTransformedFirstMain
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring

theorem quadraticGcdPairs_empty_of_not_squarefree (N D : ℕ) (hD : ¬ Squarefree D) :
    quadraticGcdPairs N D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  have hs := (Finset.mem_product.mp hz).1
  have hsf := (Finset.mem_filter.mp hs).2.2
  apply hD
  rw [← hg]
  exact hsf.squarefree_of_dvd (Nat.gcd_dvd_left z.1 z.2)

noncomputable def quadraticMomentMainDifference (M N K : ℕ) (v : ℕ → ℂ) : ℂ :=
  quadraticGcdRemainder N v (fun D z => quadraticPairMainDifference M D (quadraticPairKernel z.1 z.2) K)

noncomputable def quadraticMainComparisonCost (ε : ℝ) (N D K : ℕ) (T : ℝ) : ℝ :=
  ((K * D ^ 2 : ℕ) : ℝ) ^ ε * (N : ℝ) ^ ε * (D : ℝ) ^ ε / Real.sqrt K * T

theorem quadratic_moment_main_comparison (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 0 < M → 0 < K →
      ∀ T : ℕ → ℝ, (∀ D ∈ Finset.Icc 1 N, 0 ≤ T D) →
      (∀ D ∈ Finset.Icc 1 N, Squarefree D → Odd D → QuadraticSieveBound (K * D ^ 2) N (T D)) →
      ∀ v : ℕ → ℂ,
      ‖quadraticMomentMainDifference M N K v‖ ≤
        C * Real.sqrt M * (∑ D ∈ Finset.Icc 1 N, quadraticMainComparisonCost ε N D K (T D)) *
          quadraticSieveEnergy N v := by
  obtain ⟨C, hC, hc⟩ := quadratic_transformed_main_comparison quadraticSieveWeight ε hε
  refine ⟨C, hC, ?_⟩
  intro M N K hM hK T hT hbound v
  have hEn : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp (D : ℕ) (hD : D ∈ Finset.Icc 1 N) :
      ‖∑ z ∈ quadraticGcdPairs N D,
        v z.1 * conj (v z.2) * quadraticPairMainDifference M D (quadraticPairKernel z.1 z.2) K‖ ≤
      C * Real.sqrt M * quadraticMainComparisonCost ε N D K (T D) * quadraticSieveEnergy N v := by
    have hTD := hT D hD
    by_cases hsf : Squarefree D
    · by_cases ho : Odd D
      · rw [quadratic_pair_main_difference_sum]
        convert hc M (by exact_mod_cast hM) N D K hsf ho hK (T D) (hT D hD)
          (hbound D hD hsf ho) v using 1
        unfold quadraticMainComparisonCost
        ring
      · rw [quadraticGcdPairs_empty_of_not_odd N D ho, Finset.sum_empty, norm_zero]
        unfold quadraticMainComparisonCost
        positivity
    · rw [quadraticGcdPairs_empty_of_not_squarefree N D hsf, Finset.sum_empty, norm_zero]
      unfold quadraticMainComparisonCost
      positivity
  unfold quadraticMomentMainDifference quadraticGcdRemainder
  calc
    _ ≤ ∑ D ∈ Finset.Icc 1 N,
        C * Real.sqrt M * quadraticMainComparisonCost ε N D K (T D) * quadraticSieveEnergy N v :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

theorem quadratic_off_diagonal_main_comparison (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ, 0 < M → 0 < K →
      ∀ T : ℕ → ℝ, (∀ D ∈ Finset.Icc 1 N, 0 ≤ T D) →
      (∀ D ∈ Finset.Icc 1 N, Squarefree D → Odd D → QuadraticSieveBound (K * D ^ 2) N (T D)) →
      ∀ v : ℕ → ℂ,
      ‖quadraticGcdRemainder N v (fun D z => if z.1 = z.2 then 0 else
        quadraticPairMainDifference M D (quadraticPairKernel z.1 z.2) K)‖ ≤
        C * Real.sqrt M * (∑ D ∈ Finset.Icc 1 N, quadraticMainComparisonCost ε N D K (T D)) *
          quadraticSieveEnergy N v := by
  obtain ⟨C, hC, hc⟩ := quadratic_moment_main_comparison ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro M N K hM hK T hT hbound v
  have hh := quadratic_off_diagonal_of_bound N
    (fun D z => quadraticPairMainDifference M D (quadraticPairKernel z.1 z.2) K)
    (fun w => hc M N K hM hK T hT hbound w) v
  convert hh using 1
  ring

end Ostmann

end OAI

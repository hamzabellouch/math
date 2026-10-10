import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRootCharacter

namespace OAI

/-! # The two original Poisson main terms and their proved comparison

The common real factor (sqrt M / 2 times the fixed smoothing integral) is omitted
from both terms. All character, totient and gcd factors are retained.
-/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticFirstMain (N D K : ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N D,
    b z.1 * conj (b z.2) *
      ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2) *
      ((∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        quadraticRootCharacter (quadraticPairKernel z.1 z.2) e) *
        ∑ v ∈ oddSquarefreeRange K, quadraticRootCharacter (quadraticPairKernel z.1 z.2) v)

noncomputable def quadraticSecondMain (N D K : ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N D,
    b z.1 * conj (b z.2) *
      ((Nat.totient (quadraticPairKernel z.1 z.2 * D) : ℂ) / (quadraticPairKernel z.1 z.2 * D)) *
        ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
          quadraticRootCharacter (quadraticPairKernel z.1 z.2) v

 theorem quadratic_original_main_difference {N D K : ℕ} (hD : D ≠ 0) (b : ℕ → ℂ) :
    quadraticFirstMain N D K b - quadraticSecondMain N D K b =
      quadraticMainDifference N D K b := by
  symm
  let c : ℕ × ℕ → ℂ := fun z => b z.1 * conj (b z.2) *
    ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2)
  have hexpand : quadraticMainDifference N D K b =
      ∑ w ∈ Finset.Icc 1 (K * D ^ 2), ∑ z ∈ quadraticGcdPairs N D,
        c z * ((quadraticMainGamma D K w : ℂ) * quadraticRootCharacter
          (quadraticPairKernel z.1 z.2) w) := by
    unfold quadraticMainDifference quadraticTotientKernelSum
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    dsimp only [c, quadraticRootCharacter]
    ring
  rw [hexpand, Finset.sum_comm]
  unfold quadraticFirstMain quadraticSecondMain
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
  have hDq := quadraticPairKernel_coprime_gcd
    (Finset.mem_filter.mp h₁).2.2 (Finset.mem_filter.mp h₂).2.2
  rw [hg] at hDq
  rw [← Finset.mul_sum, quadratic_root_main_identity hD hDq]
  have ht : ((quadraticPairKernel z.1 z.2 * D).totient : ℂ) /
      (quadraticPairKernel z.1 z.2 * D : ℕ) =
      ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2) *
        ((D.totient : ℂ) / D) := by
    rw [Nat.totient_mul hDq.symm]
    push_cast
    exact (div_mul_div_comm _ _ _ _).symm
  simp only [Nat.cast_mul] at ht
  rw [ht]
  dsimp only [c]
  ring

 theorem quadratic_original_main_comparison (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N D K : ℕ, Squarefree D → Odd D → 0 < K →
      ∀ T : ℝ, 0 ≤ T → QuadraticSieveBound (K * D ^ 2) N T → ∀ b : ℕ → ℂ,
      ‖quadraticFirstMain N D K b - quadraticSecondMain N D K b‖ ≤
        C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε * (N : ℝ) ^ ε * (D : ℝ) ^ ε /
          Real.sqrt (K : ℝ) * T * quadraticSieveEnergy N b := by
  obtain ⟨C, hC, hc⟩ := quadratic_main_comparison ε hε
  refine ⟨C, hC, ?_⟩
  intro N D K hD hDo hK T hT h b
  rw [quadratic_original_main_difference hD.ne_zero]
  exact hc N D K hD hDo hK T hT h b

end Ostmann

end OAI

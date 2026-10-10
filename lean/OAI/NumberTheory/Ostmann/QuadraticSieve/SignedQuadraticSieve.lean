import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveTranspose
import OAI.NumberTheory.Ostmann.QuadraticSieve.SignedSquarefreeRange

namespace OAI

/-! # The signed kernel form follows from Heath-Brown's published theorem -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticNumeratorTwist (d : ℤ) (b : ℕ → ℂ) (s : ℕ) : ℂ :=
  b s * (jacobiSym d s : ℂ)

theorem quadraticSieveEnergy_numeratorTwist_le (N : ℕ) (d : ℤ) (b : ℕ → ℂ) :
    quadraticSieveEnergy N (quadraticNumeratorTwist d b) ≤ quadraticSieveEnergy N b := by
  apply Finset.sum_le_sum
  intro s _
  rcases jacobiSym.trichotomy d s with h | h | h <;>
    simp [quadraticNumeratorTwist, h]

theorem quadraticTransposeSum_mul (N : ℕ) (b : ℕ → ℂ) (d u : ℤ) :
    quadraticTransposeSum N b (d * u) =
      quadraticTransposeSum N (quadraticNumeratorTwist d b) u := by
  apply Finset.sum_congr rfl
  intro s _
  simp only [jacobiSym.mul_left, Int.cast_mul, quadraticNumeratorTwist, mul_assoc]

theorem quadratic_twist_sum_bound (M N : ℕ) (C ε : ℝ) (b : ℕ → ℂ) (d : ℤ)
    (hK : 0 ≤ C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N))
    (hb : ∀ b' : ℕ → ℂ,
      (∑ v ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b' v‖ ^ 2) ≤
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b') :
    (∑ v ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b (d * v)‖ ^ 2) ≤
      C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b := by
  calc
    _ = ∑ v ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N (quadraticNumeratorTwist d b) v‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [quadraticTransposeSum_mul]
    _ ≤ _ := (hb (quadraticNumeratorTwist d b)).trans
      (mul_le_mul_of_nonneg_left (quadraticSieveEnergy_numeratorTwist_le N d b) hK)

/-- Four numerator twists and two reciprocity classes suffice, including the
kernels `1` and `-1`. The constant here is exactly eight times the published one. -/
theorem quadratic_signed_bound (P : PublishedQuadraticLargeSieve)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 1 ≤ M → 1 ≤ N → ∀ b : ℕ → ℂ,
      (∑ u ∈ signedSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2) ≤
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b := by
  obtain ⟨C, hC, hbound⟩ := quadratic_transpose_odd_bound P ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro M N hM hN b
  have hK : 0 ≤ C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) := by positivity
  calc
    _ ≤ ∑ d ∈ quadraticSigns, ∑ v ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N b (d * v)‖ ^ 2 :=
      by
        exact sum_signedSquarefreeRange_le M _ (fun _ => sq_nonneg _)
    _ ≤ ∑ _d ∈ quadraticSigns,
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b := by
      apply Finset.sum_le_sum
      intro d _
      exact quadratic_twist_sum_bound M N C ε b d hK (hbound M N hM hN)
    _ = _ := by
      rw [Finset.sum_const, show quadraticSigns.card = 4 by norm_num [quadraticSigns]]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring

/-- The genuine finite kernel-count consequence. Its sole analytic hypothesis
is the published large sieve, and the test array is shared by all kernels. -/
theorem quadratic_kernel_count (P : PublishedQuadraticLargeSieve)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N : ℕ) (b : ℕ → ℂ) (U : Finset ℤ) (a : ℝ),
      1 ≤ M → 1 ≤ N → 0 < a → U ⊆ signedSquarefreeRange M →
      (∀ u ∈ U, a ≤ ‖quadraticTransposeSum N b u‖) →
      (U.card : ℝ) ≤ C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) *
        quadraticSieveEnergy N b / a ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := quadratic_signed_bound P ε hε
  refine ⟨C, hC, ?_⟩
  intro M N b U a hM hN ha hU htest
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  calc
    (U.card : ℝ) * a ^ 2 = ∑ _u ∈ U, a ^ 2 := by simp
    _ ≤ ∑ u ∈ U, ‖quadraticTransposeSum N b u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact pow_le_pow_left₀ ha.le (htest u hu) 2
    _ ≤ ∑ u ∈ signedSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hU (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hbound M N hM hN b

end Ostmann

end OAI

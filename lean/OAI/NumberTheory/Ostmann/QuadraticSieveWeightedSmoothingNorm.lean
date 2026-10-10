import OAI.NumberTheory.Ostmann.QuadraticSieveLargeGcd
import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedSmoothingDyadic

namespace OAI

namespace Ostmann.QuadraticSieve

theorem sum_jacobi_reverse_twist (S : Finset ℕ) (a : ℕ → ℂ)
    {r v : ℕ} (hv : Odd v) (hS : ∀ s ∈ S, Odd s) (hrv : r % 4 = v % 4) :
    (∑ s ∈ S, a s * (jacobiSym (s : ℤ) v : ℂ)) =
      ∑ s ∈ S, twistedCoefficients 1 r a s * (jacobiSym (v : ℤ) s : ℂ) := by
  apply Finset.sum_congr rfl
  intro s hs
  have ht : reciprocityTwist s v = reciprocityTwist r s := by
    rw [reciprocityTwist_congr_left hrv,
      reciprocityTwist_eq_if s hv, reciprocityTwist_eq_if v (hS s hs)]
    simp only [and_comm]
  rw [jacobi_reciprocity_twist (hS s hs) hv, ht, Int.cast_mul]
  simp only [twistedCoefficients, jacobiSym.one_left, Int.cast_one, mul_one]
  ring

theorem jacobiEnergy_le_two_numerator_twists (V S : Finset ℕ) (a : ℕ → ℂ)
    (hV : ∀ v ∈ V, Odd v) (hS : ∀ s ∈ S, Odd s) :
    jacobiEnergy V S a ≤ numeratorEnergy 1 V S (twistedCoefficients 1 1 a) +
      numeratorEnergy 1 V S (twistedCoefficients 1 3 a) := by
  unfold jacobiEnergy numeratorEnergy
  simp only [one_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (hV v hv)) with hv1 | hv3
  · rw [sum_jacobi_reverse_twist S a (r := 1) (hV v hv) hS (by simpa using hv1.symm)]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [sum_jacobi_reverse_twist S a (r := 3) (hV v hv) hS (by simpa using hv3.symm)]
    exact le_add_of_nonneg_left (sq_nonneg _)

theorem quadraticNorm_dyadic_le_smoothingNorm {M K : ℕ} (hM : 0 < M) (hK : K ≤ M)
    (S : Finset ℕ) (hS : ∀ s ∈ S, Odd s) :
    quadraticNorm (dyadicSquarefreeRows M) S ≤ 2 * smoothingNorm M K S := by
  apply quadraticNorm_le_of_bound _ _ (mul_nonneg (by norm_num) (smoothingNorm_nonneg _ _ _))
  intro a
  calc
    _ ≤ numeratorEnergy 1 (dyadicSquarefreeRows M) S (twistedCoefficients 1 1 a) +
        numeratorEnergy 1 (dyadicSquarefreeRows M) S (twistedCoefficients 1 3 a) :=
      jacobiEnergy_le_two_numerator_twists _ S a
        (fun v hv => (mem_dyadicSquarefreeRows.mp hv).2.2.1) hS
    _ ≤ smoothingNorm M K S * coefficientEnergy S (twistedCoefficients 1 1 a) +
        smoothingNorm M K S * coefficientEnergy S (twistedCoefficients 1 3 a) :=
      add_le_add (numeratorEnergy_dyadic_le_smoothingNorm hM hK S _)
        (numeratorEnergy_dyadic_le_smoothingNorm hM hK S _)
    _ ≤ smoothingNorm M K S * coefficientEnergy S a +
        smoothingNorm M K S * coefficientEnergy S a :=
      add_le_add
        (mul_le_mul_of_nonneg_left (coefficientEnergy_twisted_le S a 1 1) (smoothingNorm_nonneg _ _ _))
        (mul_le_mul_of_nonneg_left (coefficientEnergy_twisted_le S a 1 3) (smoothingNorm_nonneg _ _ _))
    _ = _ := by ring

theorem smoothing_large_gcd_removal (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M K N D : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      S ⊆ oddSquarefreeUpTo N → 0 < D →
      smoothingEnergy M K S a ≤
        (∑ d ∈ Finset.Icc 1 D,
          ‖weightedGcdCorrelation (smoothingRows M K) S (smoothingWeight M) a d‖) +
        C * (N : ℝ) ^ ε * smoothingNorm M K (oddSquarefreeUpTo (N / D)) * coefficientEnergy S a := by
  obtain ⟨C, hC, hbound⟩ := weighted_large_gcd_removal ε hε
  refine ⟨C, hC, ?_⟩
  intro M K N D S a hS hD
  exact hbound (smoothingRows M K) S (smoothingWeight M) a N D
    (fun m hm => smoothingWeight_nonneg M m) hS hD

end Ostmann.QuadraticSieve

end OAI

import OAI.NumberTheory.Ostmann.QuadraticSieveInitial
import OAI.NumberTheory.Ostmann.QuadraticSieveNormSupport

namespace OAI

namespace Ostmann.QuadraticSieve

theorem quadraticNorm_initial (U S : ℕ) (hU : 0 < U) :
    quadraticNorm (oddSquarefreeUpTo U) (oddSquarefreeUpTo S) ≤
      32 * ((S + 1 : ℕ) + (U : ℝ) ^ 2) := by
  have hsub : oddSquarefreeUpTo S ⊆ Finset.range (S + 1) := by
    intro n hn
    have h := mem_oddSquarefreeUpTo.mp hn
    simpa only [Finset.mem_range] using Nat.lt_succ_of_le h.2.1
  apply quadraticNorm_le_of_bound _ _ (by positivity)
  intro a
  have h := initial_character_sieve U (S + 1) (supportCoefficients (oddSquarefreeUpTo S) a) hU
  change jacobiEnergy (oddSquarefreeUpTo U) (Finset.range (S + 1))
      (supportCoefficients (oddSquarefreeUpTo S) a) ≤
        _ * coefficientEnergy (Finset.range (S + 1))
          (supportCoefficients (oddSquarefreeUpTo S) a) at h
  simpa only [jacobiEnergy_supportCoefficients _ hsub,
    coefficientEnergy_supportCoefficients hsub] using h

theorem quadraticNorm_initial_swapped (U S : ℕ) (hU : 0 < U) (hS : 0 < S) :
    quadraticNorm (oddSquarefreeUpTo U) (oddSquarefreeUpTo S) ≤
      128 * ((U : ℝ) + (S : ℝ) ^ 2) := by
  have hodd (T : ℕ) : ∀ n ∈ oddSquarefreeUpTo T, Odd n :=
    fun _ hn => (mem_oddSquarefreeUpTo.mp hn).2.2.1
  have hsym := quadraticNorm_le_two_swap (oddSquarefreeUpTo U) (oddSquarefreeUpTo S)
    (hodd U) (hodd S)
  have hi := quadraticNorm_initial S U hS
  have hu : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hs : (0 : ℝ) ≤ S := by positivity
  calc
    _ ≤ 2 * quadraticNorm (oddSquarefreeUpTo S) (oddSquarefreeUpTo U) := hsym
    _ ≤ 2 * (32 * ((U + 1 : ℕ) + (S : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hi (by norm_num)
    _ ≤ _ := by push_cast; nlinarith [sq_nonneg (S : ℝ)]

end Ostmann.QuadraticSieve

end OAI

import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSetWeights

namespace OAI

/-! # Exact pushforward for two independent prime products -/

namespace JointDickman

open Finset

theorem primeProductPair_weighted_sum (P : Finset ℕ) (z : ℝ)
    (S : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) :
    (∑ ac ∈ S, f ac * (primeProductMass P z ac.1 * primeProductMass P z ac.2)) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ S then
          f (∏ p ∈ A, p, ∏ p ∈ D, p) *
            (bernoulliSubsetMass P (fun p => z / p) A * bernoulliSubsetMass P (fun p => z / p) D)
        else 0 := by
  classical
  unfold primeProductMass
  simp_rw [sum_mul_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  have hpoint (ac : ℕ × ℕ) :
      f ac * ((if (∏ p ∈ A, p) = ac.1 then bernoulliSubsetMass P (fun p => z / p) A else 0) *
        (if (∏ p ∈ D, p) = ac.2 then bernoulliSubsetMass P (fun p => z / p) D else 0)) =
      if ac = (∏ p ∈ A, p, ∏ p ∈ D, p) then
        f ac * (bernoulliSubsetMass P (fun p => z / p) A * bernoulliSubsetMass P (fun p => z / p) D)
      else 0 := by
    rcases ac with ⟨a, c⟩
    by_cases ha : (∏ p ∈ A, p) = a <;> by_cases hc : (∏ p ∈ D, p) = c
    all_goals simp only [ha, hc, ite_true, ite_false, zero_mul, mul_zero, Prod.mk.injEq]
    all_goals simp_all only [eq_comm, and_self, and_true, and_false, ite_false]
  simp_rw [hpoint]
  simp

theorem primeProductPair_sum_event (P : Finset ℕ) (z : ℝ) (S : Finset (ℕ × ℕ)) :
    (∑ ac ∈ S, primeProductMass P z ac.1 * primeProductMass P z ac.2) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ S then
          bernoulliSubsetMass P (fun p => z / p) A * bernoulliSubsetMass P (fun p => z / p) D
        else 0 := by
  simpa only [one_mul] using primeProductPair_weighted_sum P z S (fun _ => 1)

end JointDickman

end OAI

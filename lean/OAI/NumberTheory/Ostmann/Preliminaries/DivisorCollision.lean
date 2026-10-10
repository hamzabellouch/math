import OAI.NumberTheory.Ostmann.Preliminaries.DivisorLog
import OAI.NumberTheory.Ostmann.Preliminaries.ProjectedMass

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def congruenceCollisionEnergy (p : ℕ) (n : α → ℕ) (μ : α → ℝ) : ℝ :=
  ∑ a, ∑ b, if (n a : ZMod p) = (n b : ZMod p) then μ a * μ b else 0

omit [DecidableEq α] in
theorem congruenceCollisionEnergy_eq_projected (p : ℕ) [NeZero p]
    (n : α → ℕ) (μ : α → ℝ) :
    congruenceCollisionEnergy p n μ =
      massEnergy (projectedMass (fun a => (n a : ZMod p)) μ) :=
  (projectedMass_energy (fun a => (n a : ZMod p)) μ).symm

omit [DecidableEq α] in
theorem neg_projectedMass_energy (p : ℕ) [NeZero p] (n : α → ℕ) (μ : α → ℝ) :
    massEnergy (projectedMass (fun a => -(n a : ZMod p)) μ) =
      congruenceCollisionEnergy p n μ := by
  rw [projectedMass_energy]
  simp only [neg_inj, congruenceCollisionEnergy]

omit [DecidableEq α] in
theorem weighted_collision_pair_identity (P : Finset ℕ) (n : α → ℕ) (μ : α → ℝ) :
    (∑ p ∈ P, Real.log p * congruenceCollisionEnergy p n μ) =
      ∑ a, ∑ b, (μ a * μ b) *
        ∑ p ∈ P.filter (fun p => (n a : ZMod p) = (n b : ZMod p)), Real.log p := by
  simp only [congruenceCollisionEnergy, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> ring

theorem weighted_collision_energy_le (P : Finset ℕ) (n : α → ℕ) (μ : α → ℝ)
    (X : ℕ) (hX : 1 ≤ X) (hn : Function.Injective n) (hbound : ∀ a, n a ≤ X)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hμ : ∀ a, 0 ≤ μ a)
    (hmass : ∑ a, μ a = 1) :
    (∑ p ∈ P, Real.log p * congruenceCollisionEnergy p n μ) ≤
      Real.log X + (∑ p ∈ P, Real.log p) * massEnergy μ := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hcost (a b : α) :
      (∑ p ∈ P.filter (fun p => (n a : ZMod p) = (n b : ZMod p)), Real.log p) ≤
        Real.log X + if a = b then (∑ p ∈ P, Real.log p) else 0 := by
    by_cases hab : a = b
    · subst b
      simpa using (add_le_add_right hlog (∑ p ∈ P, Real.log p))
    · simpa [hab] using sum_log_congruent_primes_le P (n a) (n b) X
        (fun h => hab (hn h)) (hbound a) (hbound b) hprime
  rw [weighted_collision_pair_identity]
  calc
    (∑ a, ∑ b, (μ a * μ b) *
        ∑ p ∈ P.filter (fun p => (n a : ZMod p) = (n b : ZMod p)), Real.log p) ≤
      ∑ a, ∑ b, (μ a * μ b) *
        (Real.log X + if a = b then (∑ p ∈ P, Real.log p) else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hcost a b) (mul_nonneg (hμ a) (hμ b))
    _ = Real.log X + (∑ p ∈ P, Real.log p) * massEnergy μ := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      simp only [hmass, mul_one, one_mul, massEnergy, pow_two]
      ring

theorem weighted_prime_collision_energy_le (Q X : ℕ) (n : α → ℕ) (μ : α → ℝ)
    (hX : 1 ≤ X) (hn : Function.Injective n) (hbound : ∀ a, n a ≤ X)
    (hμ : ∀ a, 0 ≤ μ a) (hmass : ∑ a, μ a = 1)
    {M : ℝ} (hcap : ∀ a, μ a ≤ M) :
    (∑ p ∈ Q.primesLE, Real.log p * congruenceCollisionEnergy p n μ) ≤
      Real.log X + Real.log 4 * Q * M := by
  have hE : massEnergy μ ≤ M := massEnergy_le_cap μ hμ hmass hcap
  have hM : 0 ≤ M := (massEnergy_nonneg μ).trans hE
  have hlogs : 0 ≤ ∑ p ∈ Q.primesLE, Real.log p :=
    Finset.sum_nonneg (fun p hp => Real.log_nonneg
      (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
  calc
    (∑ p ∈ Q.primesLE, Real.log p * congruenceCollisionEnergy p n μ) ≤
        Real.log X + (∑ p ∈ Q.primesLE, Real.log p) * massEnergy μ :=
      weighted_collision_energy_le Q.primesLE n μ X hX hn hbound
        (fun p hp => (Nat.mem_primesLE.mp hp).2) hμ hmass
    _ ≤ Real.log X + (∑ p ∈ Q.primesLE, Real.log p) * M :=
      add_le_add_right (mul_le_mul_of_nonneg_left hE hlogs) _
    _ ≤ Real.log X + Real.log 4 * Q * M :=
      add_le_add_right (mul_le_mul_of_nonneg_right (sum_log_primesLE_le Q) hM) _

end Ostmann.Preliminaries

end OAI

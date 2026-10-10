import OAI.Combinatorics.ContingencyTables.Transport.IntegerPairRecursion
import OAI.Combinatorics.ContingencyTables.Transport.SignedTransport

namespace OAI

/-! # Integer leaf cliques, allowing invalid holes of zero weight -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open SignedTransport

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The leaf-clique estimate for raw masses. Invalid removals may have
zero mass; no artificial positive weight is assigned to those vertices. -/
theorem raw_leaf_transport (m h H : I → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hbalance : ∑ i, m i * h i = 0) :
    (∑ i, m i * h i * H i) ^ 2 ≤
      (∑ i, m i * h i ^ 2) * cliqueEnergy m (fun _ => 1) H := by
  cases isEmpty_or_nonempty I with
  | inl he => simp [cliqueEnergy]
  | inr hn =>
    obtain ⟨hub, _, hhub⟩ := Finset.exists_max_image Finset.univ m Finset.univ_nonempty
    have hdemand : (∑ i, m i * h i * (H i-H hub)) = ∑ i, m i * h i * H i := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hbalance,
        zero_mul, sub_zero]
    have hcs : (∑ i, m i * h i * (H i-H hub)) ^ 2 ≤
        (∑ i, m i * h i ^ 2) * ∑ i, m i * (H i-H hub) ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      · intro i _
        exact mul_nonneg (hm i) (sq_nonneg _)
      · intro i _
        exact mul_nonneg (hm i) (sq_nonneg _)
      · intro i _
        exact le_of_eq (by ring)
    have hstar : (∑ i, m i * (H i-H hub) ^ 2) ≤ cliqueEnergy m (fun _ => 1) H := by
      have hs := star_energy_le
        (fun i j => min (m i) (m j) * (H i-H j)^2)
        (fun i j => mul_nonneg (le_min (hm i) (hm j)) (sq_nonneg _))
        (by intro i j; rw [min_comm]; ring) (by intro i; simp) hub
      simp_rw [min_eq_left (hhub _ (Finset.mem_univ _))] at hs
      simpa only [cliqueEnergy, one_mul] using hs
    rw [hdemand] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_left hstar
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hm i) (sq_nonneg _))))

/-- Instantiation at the actual one-removal weights of an integer display. -/
theorem integer_leaf_transport (F : (I → ℕ) → ℝ) (z : I → ℕ)
    (h H : I → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hbalance : ∑ i, oneHole F z i * h i = 0) :
    (∑ i, oneHole F z i * h i * H i)^2 ≤
      holePotential F z h * cliqueEnergy (oneHole F z) (fun _ => 1) H := by
  exact raw_leaf_transport (oneHole F z) h H
    (fun i => by unfold oneHole; split_ifs; exact hF _; exact le_rfl) hbalance

end ContingencyTables.IntegerWeightedTransport

end OAI

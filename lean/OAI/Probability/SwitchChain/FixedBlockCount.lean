import OAI.Probability.SwitchChain.FixedBlockPartitions
import OAI.Probability.SwitchChain.FiberLabelCounting

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Problem315.FixedBlock

variable {α β : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α] [Fintype β] [DecidableEq β]

def partitionEquivColorings (sizes : Fin 3 → ℕ) :
    Partition (α := α) sizes ≃
    FiberLabelCounting.PrescribedFiberColorings (V := α) sizes :=
  Equiv.subtypeEquivRight (fun g => by simp [Fintype.card_subtype, row])

include sectionDecidableEqα in
theorem partition_nonempty (sizes : Fin 3 → ℕ)
    (hsum : ∑ i, sizes i = Fintype.card α) :
    Nonempty (Partition (α := α) sizes) := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have h := FiberLabelCounting.prescribedFiberColorings_nonempty (V := α) sizes hsum
  exact h.map (fun c => (partitionEquivColorings (α := α) sizes).symm c)

theorem partition_card_mul_factorials (sizes : Fin 3 → ℕ)
    (hne : Nonempty (Partition (α := α) sizes)) :
    Fintype.card (Partition (α := α) sizes) * (∏ i, (sizes i).factorial) =
      (Fintype.card α).factorial := by
  rw [Fintype.card_congr (partitionEquivColorings sizes)]
  have h := FiberLabelCounting.prescribedFiberColorings_card_mul_factorials (V := α) sizes
    (hne.map (fun c => partitionEquivColorings (α := α) sizes c))
  simpa only [← Nat.card_eq_fintype_card] using h

theorem partition_card_real (sizes : Fin 3 → ℕ)
    (hne : Nonempty (Partition (α := α) sizes)) :
    (Fintype.card (Partition (α := α) sizes) : ℝ) =
      (Fintype.card α).factorial / ∏ i, ((sizes i).factorial : ℝ) := by
  have hp : (∏ i, ((sizes i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero (sizes i))
  apply (eq_div_iff hp).mpr
  exact_mod_cast partition_card_mul_factorials sizes hne

theorem partition_pair_card_real (sizesU sizesW : Fin 3 → ℕ)
    (hU : Nonempty (Partition (α := α) sizesU))
    (hW : Nonempty (Partition (α := β) sizesW)) :
    (Fintype.card (Partition (α := α) sizesU × Partition (α := β) sizesW) : ℝ) =
      ((Fintype.card α).factorial * (Fintype.card β).factorial : ℝ) /
        ∏ i, (((sizesU i).factorial : ℝ) * ((sizesW i).factorial : ℝ)) := by
  rw [Fintype.card_prod, Nat.cast_mul, partition_card_real sizesU hU,
    partition_card_real sizesW hW, div_mul_div_comm, Finset.prod_mul_distrib]

theorem partition_pair_card_real_of_sum (sizesU sizesW : Fin 3 → ℕ)
    (hU : ∑ i, sizesU i = Fintype.card α)
    (hW : ∑ i, sizesW i = Fintype.card β) :
    (Fintype.card (Partition (α := α) sizesU × Partition (α := β) sizesW) : ℝ) =
      ((Fintype.card α).factorial * (Fintype.card β).factorial : ℝ) /
        ∏ i, (((sizesU i).factorial : ℝ) * ((sizesW i).factorial : ℝ)) :=
  partition_pair_card_real sizesU sizesW
    (partition_nonempty sizesU hU) (partition_nonempty sizesW hW)

def pairSizeWeight (sizesU sizesW : Fin 3 → ℕ) : ℝ :=
  (∏ i, (((sizesU i).factorial : ℝ) * ((sizesW i).factorial : ℝ)))⁻¹

theorem uniform_size_expectation {K : Type*} [Fintype K]
    (sizesU sizesW : K → Fin 3 → ℕ)
    (hU : ∀ k, ∑ i, sizesU k i = Fintype.card α)
    (hW : ∀ k, ∑ i, sizesW k i = Fintype.card β) (f : K → ℝ) :
    (∑ p : (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)),
      f p.1) /
      Fintype.card (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)) =
    (∑ k, pairSizeWeight (sizesU k) (sizesW k) * f k) /
      ∑ k, pairSizeWeight (sizesU k) (sizesW k) := by
  let C : ℝ := (Fintype.card α).factorial * (Fintype.card β).factorial
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (Fintype.card α))
      (by exact_mod_cast Nat.factorial_ne_zero (Fintype.card β))
  have hc (k : K) :
      (Fintype.card (Partition (α := α) (sizesU k) ×
        Partition (α := β) (sizesW k)) : ℝ) =
      C * pairSizeWeight (sizesU k) (sizesW k) := by
    simpa only [C, pairSizeWeight, div_eq_mul_inv] using
      partition_pair_card_real_of_sum (sizesU k) (sizesW k) (hU k) (hW k)
  have hn : (∑ p : (Σ k, Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)), f p.1) =
      C * ∑ k, pairSizeWeight (sizesU k) (sizesW k) * f k := by
    rw [Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, mul_assoc]
  have hd : (Fintype.card (Σ k, Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)) : ℝ) =
      C * ∑ k, pairSizeWeight (sizesU k) (sizesW k) := by
    rw [Fintype.card_sigma, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => hc k)
  rw [hn, hd, mul_div_mul_left _ _ hC]

theorem uniform_family_expectation {K : Type*} [Fintype K]
    (sizesU sizesW : K → Fin 3 → ℕ)
    (hU : ∀ k, ∑ i, sizesU k i = Fintype.card α)
    (hW : ∀ k, ∑ i, sizesW k i = Fintype.card β)
    (f : ∀ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k) → ℝ) :
    (∑ p : (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)),
      f p.1 p.2) /
      Fintype.card (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)) =
    (∑ k, pairSizeWeight (sizesU k) (sizesW k) *
      ((∑ p, f k p) /
        Fintype.card (Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)))) /
      ∑ k, pairSizeWeight (sizesU k) (sizesW k) := by
  rw [← uniform_size_expectation sizesU sizesW hU hW]
  congr 1
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨u⟩ := partition_nonempty (sizesU k) (hU k)
  obtain ⟨w⟩ := partition_nonempty (sizesW k) (hW k)
  have : Nonempty (Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)) := ⟨(u, w)⟩
  have hc : (Fintype.card (Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change (∑ p, f k p) =
    ∑ _p : Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k),
      (∑ p, f k p) / Fintype.card (Partition (α := α) (sizesU k) ×
        Partition (α := β) (sizesW k))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Problem315.FixedBlock

end

end OAI

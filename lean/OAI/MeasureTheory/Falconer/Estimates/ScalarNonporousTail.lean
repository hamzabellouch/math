import OAI.MeasureTheory.Falconer.Estimates.ScalarPorousEndpoints

namespace OAI

/-! The terminal run past the last selected porous endpoint consists
 entirely of the already-counted nonporous blocks. -/
namespace Falconer.Regularization

 theorem scalar_nonporous_tail_subset {M B C t : ℕ} (k n : ℕ → ℕ)
    (hend : ∀ i ∈ scalarPorousLevels M B C k n, i < t) :
    Finset.Ico t M ⊆ scalarNonporousLevels M B C k n := by
  classical
  intro i hi
  have hit := Finset.mem_Ico.mp hi
  by_contra hnot
  have hp : i ∈ scalarPorousLevels M B C k n := by
    rw [scalar_porous_nonporous_partition]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hit.2,hnot⟩
  have hh := hend i hp
  omega

 theorem scalar_nonporous_tail_length {M B C t : ℕ} (k n : ℕ → ℕ)
    (hend : ∀ i ∈ scalarPorousLevels M B C k n, i < t) :
    M-t ≤ (scalarNonporousLevels M B C k n).card := by
  have hh := Finset.card_le_card (scalar_nonporous_tail_subset k n hend)
  simpa only [Nat.card_Ico] using hh

 theorem scalar_nonporous_tail_weight {M B C t : ℕ} {L : Finset (CellPath 1)}
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i))
    (hend : ∀ i ∈ scalarPorousLevels M B C k n, i < t) :
    (∑ i ∈ Finset.Ico t M, k i) ≤ B*(scalarNonporousLevels M B C k n).card := by
  have hk : ∀ i ∈ Finset.Ico t M, k i ≤ B := by
    intro i hi
    have hh := (hlevel i (Finset.mem_Ico.mp hi).2).exponent_le
    rw [Nat.mul_add,Nat.mul_one] at hh
    omega
  calc
    _ ≤ ∑ _i ∈ Finset.Ico t M, B := Finset.sum_le_sum hk
    _ = B*(M-t) := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left B (scalar_nonporous_tail_length k n hend)

end Falconer.Regularization

end OAI

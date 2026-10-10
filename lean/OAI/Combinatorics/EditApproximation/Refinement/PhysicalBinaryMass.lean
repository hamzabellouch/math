import OAI.Combinatorics.EditApproximation.Binary.BinaryWarmupAverage
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalRefinement

namespace OAI

/-! The child mass is built from the actual gathered warmup words. The
mean and construction of its finite input list both contribute to work. -/

namespace EditApproximation

def physicalWarmupMassWithWork {ny : ℕ} (T : ℕ)
    (words : ℕ → TargetInterval ny → BinaryFraction) (query : TargetInterval ny) :
    BinaryFraction × ℕ :=
  let mean := BinaryFraction.warmupAverageWithWork (List.ofFn fun j : Fin T => words j.val query)
  (mean.1, mean.2 + T + 1)

theorem physicalWarmupMassWithWork_value {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F T : ℕ) (A : ℚ) (node : PhysicalNode M J)
    (words : ℕ → TargetInterval target.length → BinaryFraction)
    (hwords : ∀ j < T, ∀ r, (words j r).value = physicalLocalWarmup source target U N P F A j (node, r))
    (query : TargetInterval target.length) :
    (physicalWarmupMassWithWork T words query).1.value =
      physicalLocalWarmupMass source target U N P F A T (node, query) := by
  rw [physicalWarmupMassWithWork, BinaryFraction.warmupAverageWithWork_ofFn_value]
  unfold physicalLocalWarmupMass
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun j =>
    physicalLocalWarmup source target U N P F A j (node, query))]
  apply Finset.sum_congr rfl
  intro j _hj
  exact hwords j.val j.isLt query

theorem physicalWarmupMassWithWork_bounds {ny : ℕ} (T B : ℕ)
    (words : ℕ → TargetInterval ny → BinaryFraction)
    (hwords : ∀ j < T, ∀ r, (words j r).width ≤ B) (query : TargetInterval ny) :
    (physicalWarmupMassWithWork T words query).1.width ≤ BinaryFraction.warmupAverageWordBudget T B ∧
    (physicalWarmupMassWithWork T words query).2 ≤ BinaryFraction.warmupAverageBitBudget T B + T + 1 := by
  have hmean := BinaryFraction.warmupAverageWithWork_bounds
    (List.ofFn fun j : Fin T => words j.val query) B (by
      intro value hv
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      exact hwords j.val j.isLt query)
  simp only [List.length_ofFn] at hmean
  exact ⟨hmean.1, Nat.add_le_add_right (Nat.add_le_add_right hmean.2 T) 1⟩

theorem warmupAverageWordBudget_le_power (H T B : ℕ) (hH : 64 ≤ H)
    (hT : T ≤ H ^ 2) (hB : B ≤ H ^ 3) :
    BinaryFraction.warmupAverageWordBudget T B ≤ H ^ 8 := by
  have hHp : 0 < H := by omega
  have hHone : 1 ≤ H := by omega
  have hsize : Nat.size T ≤ H ^ 2 := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hT
  have h23 : H ^ 2 ≤ H ^ 3 := Nat.pow_le_pow_right hHp (by decide)
  have h35 : H ^ 3 ≤ H ^ 5 := Nat.pow_le_pow_right hHp (by decide)
  have hone : 1 ≤ H ^ 3 := one_le_pow₀ hHone
  have hproduct : T * (B + 1) ≤ 2 * H ^ 5 := by
    calc
      _ ≤ H ^ 2 * (2 * H ^ 3) := Nat.mul_le_mul hT (by omega)
      _ = 2 * H ^ 5 := by ring
  have hsmall : BinaryFraction.warmupAverageWordBudget T B ≤ 64 * H ^ 5 := by
    unfold BinaryFraction.warmupAverageWordBudget BinaryFraction.bandMassTotalStorageBudget
    nlinarith only [hsize, hB, h23, h35, hproduct, hone]
  have h64 : 64 ≤ H ^ 3 := (by omega : 64 ≤ H).trans (Nat.le_pow (by decide))
  exact hsmall.trans (by
    calc
      64 * H ^ 5 ≤ H ^ 3 * H ^ 5 := Nat.mul_le_mul_right _ h64
      _ = H ^ 8 := by ring)

end EditApproximation

end OAI

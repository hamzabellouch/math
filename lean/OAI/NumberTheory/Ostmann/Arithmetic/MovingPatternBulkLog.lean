import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkBudgets
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenMovingSamples
import OAI.NumberTheory.Ostmann.Arithmetic.RealBulkKernelPair
import OAI.NumberTheory.Ostmann.Arithmetic.BulkCoordinateInsertion

namespace OAI

/-! # The real bulk coordinates evaluate to the original pattern primes -/

namespace Ostmann
open scoped Classical

noncomputable def selectedBulkSet {σ J : Type*} [Fintype σ] (slot : J ↪ σ) : Finset σ :=
  Finset.univ.filter (fun i => i ∈ Set.range slot)

@[simp] theorem mem_selectedBulkSet {σ J : Type*} [Fintype σ] (slot : J ↪ σ) (i : σ) :
    i ∈ selectedBulkSet slot ↔ i ∈ Set.range slot := by
  simp only [selectedBulkSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem selectedBulkLogValues {σ J : Type*} [Fintype σ]
    (base : σ → ℝ) (slot : J ↪ σ) (y : J → ℝ) :
    bulkLogValues base (selectedBulkSet slot) (bulkCoordinateInsert base slot y) =
      Function.extend slot (fun j => Real.exp (y j)) base := by
  funext i
  by_cases hi : i ∈ Set.range slot
  · obtain ⟨j, rfl⟩ := hi
    have hs : slot j ∈ selectedBulkSet slot := (mem_selectedBulkSet slot _).mpr ⟨j, rfl⟩
    rw [slot.injective.extend_apply]
    simp only [bulkLogValues, hs, ite_true, bulkCoordinateInsert_at]
  · rw [Function.extend_apply' _ base i hi]
    simp only [bulkLogValues, mem_selectedBulkSet, hi, ite_false]

theorem selectedBulkLogValues_nat {σ J : Type*} [Fintype σ]
    (base value : σ → ℕ) (slot : J ↪ σ)
    (hv : ∀ i ∉ Set.range slot, value i = base i) (hp : ∀ j, 0 < value (slot j)) :
    bulkLogValues (fun i => (base i : ℝ)) (selectedBulkSet slot)
        (bulkCoordinateInsert (fun i => (base i : ℝ)) slot (fun j => Real.log (value (slot j) : ℝ))) =
      fun i => (value i : ℝ) := by
  rw [selectedBulkLogValues]
  funext i
  by_cases hi : i ∈ Set.range slot
  · obtain ⟨j, rfl⟩ := hi
    rw [slot.injective.extend_apply, Real.exp_log (by exact_mod_cast hp j)]
  · rw [Function.extend_apply' _ _ i hi, hv i hi]

theorem movingPatternBulkSet_compensationAbsent {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) :
    ∀ b i, i ∈ selectedBulkSet (movingPatternBulkEmbedding e slot) →
      (movingPatternFinBulkData e n m t small slot perm pattern b).CompensationAbsent i := by
  intro b i hi
  obtain ⟨j, rfl⟩ := (mem_selectedBulkSet _ _).mp hi
  exact movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier b j

/-- At original prime tuples the real extension has exactly the original
sharp gates and Fourier windows. This includes every boundary point. -/
theorem movingPattern_bulk_kernel_nat {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (base value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base i)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (hf : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    realValueKernelPair
      (bulkLogValues (fun i => (base i : ℝ)) (selectedBulkSet (movingPatternBulkEmbedding e slot))
        (bulkCoordinateInsert (fun i => (base i : ℝ)) (movingPatternBulkEmbedding e slot)
          (fun j => Real.log (value (movingPatternBulkEmbedding e slot j) : ℝ))))
      childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
    movingRealKernelPair value T
      (fun b => (T b).formulaNodes value hvalue childBound pivotBound
        (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hf b)
        (.prime false) (.prime true)) ψ X lo hi hlo hhi φ G L R := by
  dsimp only
  rw [selectedBulkLogValues_nat base value (movingPatternBulkEmbedding e slot) hv
    (fun j => Nat.pos_of_ne_zero (hvalue _))]
  exact realValueKernelPair_nat value hvalue childBound pivotBound _ _ ψ X lo hi hlo hhi φ G L R

end Ostmann

end OAI

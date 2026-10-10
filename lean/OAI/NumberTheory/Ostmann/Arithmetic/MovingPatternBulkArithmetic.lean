import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkFrozen
import OAI.NumberTheory.Ostmann.Arithmetic.BulkCollisionSupport

namespace OAI

/-! # Supported arithmetic of the original equality-pattern histories -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original pattern's Page and spectator factors separate on precisely
its selected bulk residues. The unchanged small and sampled data, denominator
independence and regular-list distinctness are derived from the constructor. -/
theorem movingPattern_supported_arithmetic {B C I : Type*} [Fintype I] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base i)
    (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hf : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).Frequencies (· ≠ 0))
    (hinj : Function.Injective (value ∘ movingPatternBulkEmbedding e slot))
    (hcross : ∀ i j, bulkIndexPredicate (movingPatternBulkEmbedding e slot) i ≠
      bulkIndexPredicate (movingPatternBulkEmbedding e slot) j → value i ≠ value j)
    (hout : ∀ j p, p ∈ outside → (value (movingPatternBulkEmbedding e slot j)).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r]
    (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
    (hr : R ^ (n + 1) ∣ (r : ℤ))
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (D : ∀ i, Bool → (ZMod (p i))ˣ)
    (z : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value (movingPatternBulkEmbedding e slot j) : ZMod (∏ i, bulkResidueModuli r p i)) =
      (z j : ZMod _))
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let hvalue := fun i => (hprime i).ne_zero
    movingFrequencyPageAverage value outside F E T
        (fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b)
          (.prime false) (.prime true)) R r input Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (D i) T =
    frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
        F E T childBound R r input Q y (bulkResidueEquiv r p hc z).1 *
      ∏ i, frozenBulkSpectatorHaar base n m t (fun b => movingPatternFiniteSmall e n (small b))
        (movingPatternFiniteSamples e n pattern) (D i) perm (g i)
        ((bulkResidueEquiv r p hc z).2 i) := by
  have hfixed := fun b => movingPattern_nonbulk_values e tierB tierC slot base value hv
    (small b) pattern (hsmall b) hB htier b
  exact movingSupportedArithmetic_bulk_residues base value n m (movingPatternBulkEmbedding e slot)
    hv t (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
    (fun b => (hfixed b).1) (fun b => (hfixed b).2) perm
    (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternFinBulkData_build e n m t small slot perm pattern) F E outside childBound pivotBound
    (fun i => (hprime i).ne_zero) hf (fun _ _ _ i _ => hprime i)
    (movingPatternFinBulkData_bulk_nodup e tierB tierC t small slot perm pattern hsmall hB htier)
    hinj (fun _ _ _ i _ j _ h => hcross i j h)
    (fun _ _ _ i _ hi p hp => by
      obtain ⟨j, rfl⟩ := hi
      exact hout j p hp)
    R r (movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier)
    hR hr p hc g hg D z hz input Q y

/-- Bulk collisions are already zero under the original pattern coefficient,
so inserting the distinctness indicator precedes all changes of measure. -/
theorem movingPattern_arithmetic_collision_gate {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (value : Fin (N + 1) → ℕ) (hprime : ∀ i, (value i).Prime)
    (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
    (nodes : Bool → List MovingFormulaNode) (R : ℤ) (r : ℕ) [NeZero r]
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) (A : ℂ) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    movingFrequencyPageAverage value outside F E T nodes R r input Q y * A =
      if Function.Injective (value ∘ movingPatternBulkEmbedding e slot) then
        movingFrequencyPageAverage value outside F E T nodes R r input Q y * A else 0 := by
  exact movingFrequencyPageAverage_collision_gate value n m (movingPatternBulkEmbedding e slot)
    (t false) (movingPatternFiniteSmall e n (small false)) (movingPatternFiniteSamples e n pattern false)
    outside hprime F E (movingPatternFinBulkData e n m t small slot perm pattern)
    (movingPatternFinBulkData_build e n m t small slot perm pattern false) nodes R r input Q y A

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.FrozenFrequencyAverage
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenRegularSupport

namespace OAI

/-! # The full frequency factor retains precisely the fixed nonbulk support -/

namespace Ostmann
open scoped Classical

theorem movingFrequencyPageAverage_nonbulk {σ : Type*}
    (value base : σ → ℕ) (bulk : σ → Bool) (outside : List ℕ)
    (hv : ∀ i, bulk i = false → value i = base i)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (hprime : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ b, ∀ L ∈ (T b).regularLists, (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, bulk i = true →
      ∀ p ∈ outside, (value i).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y =
      (if ∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCorePageAverage value F E T R r input Q y := by
  have hsupport : (∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      (∀ f ∈ nodes b, f.guard.frequencyBounds)) ↔
      (∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds)) := by
    apply forall_congr'
    intro b
    exact and_congr (movingRegularOutsidePairwise_frozen value base bulk outside (T b)
      hv (hprime b) (hnodup b) hinj (hcross b) (hout b)) Iff.rfl
  rw [movingFrequencyPageAverage_core]
  simp only [hsupport]

/-- For the literal formula-node list, the remaining frequency-size tests
depend on the frequency tree alone. -/
theorem movingFrequencyPageAverage_actual_nonbulk {σ : Type*}
    (value base : σ → ℕ) (bulk : σ → Bool) (outside : List ℕ)
    (hv : ∀ i, bulk i = false → value i = base i)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hprime : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ b, ∀ L ∈ (T b).regularLists, (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, bulk i = true →
      ∀ p ∈ outside, (value i).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T
      (fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b)
        (.prime false) (.prime true)) R r input Q y =
      (if ∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (T b).FrequencyBounds childBound then (1 : ℂ) else 0) *
      movingFrequencyCorePageAverage value F E T R r input Q y := by
  rw [movingFrequencyPageAverage_nonbulk value base bulk outside hv F E T _
    hprime hnodup hinj hcross hout]
  have he : (∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
      ∀ f ∈ (T b).formulaNodes value hvalue childBound pivotBound (hf b)
        (.prime false) (.prime true), f.guard.frequencyBounds) ↔
      (∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (T b).FrequencyBounds childBound) := by
    apply forall_congr'
    intro b
    exact and_congr Iff.rfl ((T b).formulaNodes_frequencyBounds value hvalue childBound
      pivotBound (hf b) (.prime false) (.prime true))
  simp only [he]

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.FrozenArithmeticFactors
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenFrequencySupport

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkIndexPredicate {σ J : Type*} (slot : J ↪ σ) (i : σ) : Bool :=
  decide (i ∈ Set.range slot)

@[simp] theorem bulkIndexPredicate_eq_true {σ J : Type*} (slot : J ↪ σ) (i : σ) :
    bulkIndexPredicate slot i = true ↔ i ∈ Set.range slot := by
  simp only [bulkIndexPredicate, decide_eq_true_eq]

@[simp] theorem bulkIndexPredicate_eq_false {σ J : Type*} (slot : J ↪ σ) (i : σ) :
    bulkIndexPredicate slot i = false ↔ i ∉ Set.range slot := by
  simp only [bulkIndexPredicate, decide_eq_false_iff_not]

noncomputable def frozenBulkFrequencyFactor {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput)
    (Q : ℕ) (y : ℝ) (a : J → (ZMod r)ˣ) : ℂ :=
  (if ∀ b, movingNonbulkOutsidePairwise base (bulkIndexPredicate slot) outside (T b) ∧
      (T b).FrequencyBounds childBound then (1 : ℂ) else 0) *
    movingFrequencyCorePageAverage (Function.extend slot (fun j => (a j).val.val) base)
      F E T R r input Q y

theorem frozenBulkFrequencyFactor_norm_le {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput)
    (Q : ℕ) (y : ℝ) (hy : 0 ≤ y) (a : J → (ZMod r)ˣ) :
    ‖frozenBulkFrequencyFactor base slot outside F E T childBound R r input Q y a‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  unfold frozenBulkFrequencyFactor
  split_ifs
  · rw [one_mul]
    exact movingFrequencyCorePageAverage_norm_le _ F E T R r input Q y hy
  · rw [zero_mul, norm_zero]
    positivity

/-- The nonbulk coprimalities stay inside the fixed frequency factor. The
only injectivity used here is the actual distinct-bulk event, removed later
under its original product prior. -/
theorem movingSupportedArithmetic_bulk_residues {σ I : Type*} [Fintype I]
    (base value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (hv : ∀ i ∉ Set.range slot, value i = base i)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (samples : Bool → MovingSampleSlots σ n)
    (hvsmall : ∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b))
    (hvsamples : ∀ b, (samples b).values value = (samples b).values base)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (T : Bool → MovingSlotData σ n)
    (hT : ∀ b, T b = buildMovingSlotData n (t b) (small b)
      (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot) (samples b))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hprime : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ b, ∀ L ∈ (T b).regularLists,
      (L.filter (bulkIndexPredicate slot)).Nodup)
    (hinj : Function.Injective (value ∘ slot))
    (hcross : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulkIndexPredicate slot i ≠ bulkIndexPredicate slot j → value i ≠ value j)
    (hout : ∀ b, ∀ L ∈ (T b).regularLists, ∀ i ∈ L, i ∈ Set.range slot →
      ∀ p ∈ outside, (value i).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r]
    (hcomp : ∀ b j, (T b).CompensationAbsent (slot j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (D : ∀ i, Bool → (ZMod (p i))ˣ)
    (z : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value (slot j) : ZMod (∏ i, bulkResidueModuli r p i)) = (z j : ZMod _))
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T
        (fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b)
          (.prime false) (.prime true)) R r input Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (D i) T =
    frozenBulkFrequencyFactor base slot outside F E T childBound R r input Q y
        (bulkResidueEquiv r p hc z).1 *
      ∏ i, frozenBulkSpectatorHaar base n m t small samples (D i) e (g i)
        ((bulkResidueEquiv r p hc z).2 i) := by
  have hinj' : ∀ i j, bulkIndexPredicate slot i = true →
      bulkIndexPredicate slot j = true → value i = value j → i = j := by
    intro i j hi hj hij
    obtain ⟨a, rfl⟩ := (bulkIndexPredicate_eq_true slot i).mp hi
    obtain ⟨b, rfl⟩ := (bulkIndexPredicate_eq_true slot j).mp hj
    exact congrArg slot (hinj hij)
  rw [movingFrequencyPageAverage_actual_nonbulk value base
    (bulkIndexPredicate slot) outside
    (fun i hi => hv i ((bulkIndexPredicate_eq_false slot i).mp hi)) hvalue childBound pivotBound F E T hf
    hprime hnodup hinj' hcross (fun b L hL i hi hb => hout b L hL i hi ((bulkIndexPredicate_eq_true slot i).mp hb))]
  rw [mul_assoc, movingCoreSpectator_bulk_residues base value n m slot hv t small samples
    hvsmall hvsamples e T hT F E R r hf hcomp hR hr p hc g hg D z hz input Q y]
  simp only [frozenBulkFrequencyFactor, mul_assoc, finite_univ_canonical]

end Ostmann

end OAI

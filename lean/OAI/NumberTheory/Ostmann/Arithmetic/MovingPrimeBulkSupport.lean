import OAI.NumberTheory.Ostmann.Arithmetic.FrozenPrimeArithmeticNorm
import OAI.NumberTheory.Ostmann.Arithmetic.BulkCollisionSupport

namespace OAI

/-! # The unchanged nonbulk guards and bulk residues under two giant primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFrequencyCorePrimeAverage_bulk_residues {σ J : Type*}
    (base value : σ → ℕ) (e : J ↪ σ) (hv : ∀ i ∉ Set.range e, value i = base i)
    (r : ℕ) [NeZero r] (a : J → (ZMod r)ˣ)
    (ha : ∀ j, (value (e j) : ZMod r) = (a j : ZMod r))
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hT : ∀ b j, (T b).CompensationAbsent (e j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (input : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ) :
    movingFrequencyCorePrimeAverage value F E T R r input Q xg y =
      movingFrequencyCorePrimeAverage (Function.extend e (fun j => (a j).val.val) base)
        F E T R r input Q xg y := by
  unfold movingFrequencyCorePrimeAverage
  apply congrArg ((Fintype.card ((ZMod r)ˣ × (ZMod r)ˣ) : ℂ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro z _
  rw [movingFrequencyCore_bulk_residues value e r a ha F E T R hf hT hR hr,
    extend_eq_of_eq_off_range e _ value base hv]

theorem movingFrequencyPrimeAverage_nonbulk {σ : Type*}
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
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ) :
    movingFrequencyPrimeAverage value outside F E T nodes R r input Q xg y =
      (if ∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCorePrimeAverage value F E T R r input Q xg y := by
  have hsupport : (∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      (∀ f ∈ nodes b, f.guard.frequencyBounds)) ↔
      (∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds)) := by
    apply forall_congr'
    intro b
    exact and_congr (movingRegularOutsidePairwise_frozen value base bulk outside (T b)
      hv (hprime b) (hnodup b) hinj (hcross b) (hout b)) Iff.rfl
  rw [movingFrequencyPrimeAverage_core]
  simp only [hsupport]

/-- For the literal formula-node list, the remaining frequency-size tests
depend on the frequency tree alone. -/
theorem movingFrequencyPrimeAverage_actual_nonbulk {σ : Type*}
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
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ) :
    movingFrequencyPrimeAverage value outside F E T
      (fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b)
        (.prime false) (.prime true)) R r input Q xg y =
      (if ∀ b, movingNonbulkOutsidePairwise base bulk outside (T b) ∧
        (T b).FrequencyBounds childBound then (1 : ℂ) else 0) *
      movingFrequencyCorePrimeAverage value F E T R r input Q xg y := by
  rw [movingFrequencyPrimeAverage_nonbulk value base bulk outside hv F E T _
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

theorem movingPrimeCoreSpectator_bulk_residues {σ I : Type*} [Fintype I]
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
    (R : ℤ) (r : ℕ) [NeZero r]
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hcomp : ∀ b j, (T b).CompensationAbsent (slot j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (_hg : ∀ i, g i 0 = 0)
    (D : ∀ i, Bool → (ZMod (p i))ˣ)
    (z : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value (slot j) : ZMod (∏ i, bulkResidueModuli r p i)) = (z j : ZMod _))
    (input : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ) :
    movingFrequencyCorePrimeAverage value F E T R r input Q xg y *
      ∏ i, movingSpectatorPrimeAverage value (p i) (g i) (D i) T =
    movingFrequencyCorePrimeAverage
        (Function.extend slot (fun j => ((bulkResidueEquiv r p hc z).1 j).val.val) base)
        F E T R r input Q xg y *
      ∏ i, frozenBulkSpectatorPrime base n m t small samples (D i) e (g i)
        ((bulkResidueEquiv r p hc z).2 i) := by
  rw [movingFrequencyCorePrimeAverage_bulk_residues base value slot hv r
    (bulkResidueEquiv r p hc z).1
    (bulkResidueEquiv_frequency_lift r p hc (value ∘ slot) z hz)
    F E T R hf hcomp hR hr input Q xg y]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have ht : T = fun b => buildMovingSlotData n (t b) (small b)
      (if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot) (samples b) :=
    funext hT
  rw [ht]
  exact frozenBulkSpectatorPrime_actual base n m t small samples (D i) e value
    hvsmall hvsamples slot (g i) ((bulkResidueEquiv r p hc z).2 i)
    (bulkResidueEquiv_spectator_lift r p hc (value ∘ slot) z hz i)

theorem movingSupportedPrimeArithmetic_bulk_residues {σ I : Type*} [Fintype I]
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
    (input : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ) :
    movingFrequencyPrimeAverage value outside F E T
        (fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b)
          (.prime false) (.prime true)) R r input Q xg y *
      ∏ i, movingSpectatorPrimeAverage value (p i) (g i) (D i) T =
    frozenBulkFrequencyPrime base slot outside F E T childBound R r input Q xg y
        (bulkResidueEquiv r p hc z).1 *
      ∏ i, frozenBulkSpectatorPrime base n m t small samples (D i) e (g i)
        ((bulkResidueEquiv r p hc z).2 i) := by
  have hinj' : ∀ i j, bulkIndexPredicate slot i = true →
      bulkIndexPredicate slot j = true → value i = value j → i = j := by
    intro i j hi hj hij
    obtain ⟨a, rfl⟩ := (bulkIndexPredicate_eq_true slot i).mp hi
    obtain ⟨b, rfl⟩ := (bulkIndexPredicate_eq_true slot j).mp hj
    exact congrArg slot (hinj hij)
  rw [movingFrequencyPrimeAverage_actual_nonbulk value base
    (bulkIndexPredicate slot) outside
    (fun i hi => hv i ((bulkIndexPredicate_eq_false slot i).mp hi)) hvalue childBound pivotBound F E T hf
    hprime hnodup hinj' hcross (fun b L hL i hi hb => hout b L hL i hi ((bulkIndexPredicate_eq_true slot i).mp hb))]
  rw [mul_assoc, movingPrimeCoreSpectator_bulk_residues base value n m slot hv t small samples
    hvsmall hvsamples e T hT F E R r hf hcomp hR hr p hc g hg D z hz input Q xg y]
  simp only [frozenBulkFrequencyPrime, mul_assoc, finite_univ_canonical]

theorem movingFrequencyPrimeAverage_zero_of_bulk_collision {σ : Type*}
    (value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (outside : List ℕ)
    (hprime : ∀ i, (value i).Prime) (hbad : ¬Function.Injective (value ∘ slot))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (T : Bool → MovingSlotData σ n)
    (hT : T false = buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples)
    (nodes : Bool → List MovingFormulaNode) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ) :
    movingFrequencyPrimeAverage value outside F E T nodes R r input Q xg y = 0 := by
  have hsupport : ¬(∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      ∀ f ∈ nodes b, f.guard.frequencyBounds) := by
    intro hs
    apply hbad
    apply buildMovingSlotData_injective_of_support value n m slot t small samples outside hprime
    rw [← hT]
    exact (hs false).1
  rw [movingFrequencyPrimeAverage_core]
  simp only [hsupport, ite_false, zero_mul]

/-- Inserting the distinctness gate leaves the literal supported arithmetic
coefficient unchanged. -/
theorem movingFrequencyPrimeAverage_collision_gate {σ : Type*}
    (value : σ → ℕ) (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (outside : List ℕ)
    (hprime : ∀ i, (value i).Prime)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (T : Bool → MovingSlotData σ n)
    (hT : T false = buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples)
    (nodes : Bool → List MovingFormulaNode) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ) (A : ℂ) :
    movingFrequencyPrimeAverage value outside F E T nodes R r input Q xg y * A =
      if Function.Injective (value ∘ slot) then
        movingFrequencyPrimeAverage value outside F E T nodes R r input Q xg y * A else 0 := by
  by_cases h : Function.Injective (value ∘ slot)
  · simp only [h, ite_true]
  · rw [ite_eq_right h, movingFrequencyPrimeAverage_zero_of_bulk_collision value n m slot
      t small samples outside hprime h F E T hT nodes R r input Q xg y, zero_mul]

end Ostmann

end OAI

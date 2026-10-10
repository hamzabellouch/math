import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceSquares

namespace OAI

/-! # Uniform square-exclusion loss for each sampled representative prime -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingRepresentativeOccurrences {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (rep : σ) :=
  {j : Fin T.occurrences.length // rep ∈ (T.occurrences.get j).current.compensationSlots}

/-- Repetition across nodes costs only the actual number of occurrences. -/
theorem movingRepresentativeOccurrences_card {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (rep : σ) :
    Fintype.card (MovingRepresentativeOccurrences T rep) ≤ 2 ^ n - 1 := by
  classical
  calc
    _ ≤ Fintype.card (Fin T.occurrences.length) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by rw [Fintype.card_fin, T.occurrences_length]

/-- All unit and nonzero-row requirements for a representative's lift count
follow from the sampled prime types, not from an assumed line system. -/
theorem moving_representative_square_loss {σ : Type*} (tier : σ → ℕ)
    (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier) (rep : σ)
    (hfreq : T.Frequencies (fun s => (s : ZMod (value rep)) ≠ 0))
    (x₀ y₀ : ZMod (value rep)) (hy : y₀ ≠ 0)
    (hbase : ∀ j : MovingRepresentativeOccurrences T rep,
      let o := T.occurrences.get j.val
      let φ := MovingSlotReversal.naturalReduction (value rep) value
      φ (movingSlotLine o.path o.current).a * x₀ +
        φ (movingSlotLine o.path o.current).b * y₀ = 0)
    (F : SquareLiftPairs (value rep) x₀ y₀ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ v, ‖F v‖ ≤ B) :
    let _ : Fact (value rep).Prime := ⟨hprime rep⟩
    let φ := MovingSlotReversal.naturalReduction (value rep ^ 2) value
    ‖∑ v ∈ Finset.univ.filter (fun v : SquareLiftPairs (value rep) x₀ y₀ =>
      ∃ j : MovingRepresentativeOccurrences T rep,
        let o := T.occurrences.get j.val
        φ (movingSlotLine o.path o.current).a * v.1.1 +
          φ (movingSlotLine o.path o.current).b * v.2.1 = 0), F v‖ / (value rep : ℝ) ^ 2 ≤
      B * (2 ^ n - 1 : ℕ) / value rep := by
  classical
  let : Fact (value rep).Prime := ⟨hprime rep⟩
  let path := fun j : MovingRepresentativeOccurrences T rep => (T.occurrences.get j.val).path
  let current := fun j : MovingRepresentativeOccurrences T rep => (T.occurrences.get j.val).current
  have hu (j : MovingRepresentativeOccurrences T rep) :=
    T.occurrence_units_of_prime_types tier value hprime hdisjoint hlevels
      (T.occurrences.get j.val) (List.get_mem _ _ ) rep
      (T.occurrence_compensation_level tier hlevels _ (List.get_mem _ _) rep j.property) hfreq
  have hb := movingSlotLines_square_loss value path current
    (fun j s hs => (hu j).1 s hs) (fun j => (hu j).2) x₀ y₀ hy hbase F B hB hF
  refine hb.trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hB
  exact_mod_cast movingRepresentativeOccurrences_card T rep

end Ostmann

end OAI

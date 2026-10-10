import OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting

namespace OAI

/-! Finite endpoint, partner, and label descriptions for selected witness systems. -/

namespace TwoPointCorrelations

open Finset

/-- Two labels, a partner witness, and four bounded endpoints. Internal
relations leave the unused entries arbitrary. -/
abbrev WitnessRelationSlot (n N : ℕ) (ι : Type*) :=
  ι × ι × Fin n × Fin (N + 1) × Fin (N + 1) × Fin (N + 1) × Fin (N + 1)

/-- The mode records the two internal and the two comparison alternatives.
Every selected witness has only bounded numerical-index metadata. -/
structure WitnessSystemData (n N : ℕ) (ι : Type*) where
  mode : Fin 4
  chosen : Finset (Fin n)
  slot : chosen → WitnessRelationSlot n N ι

noncomputable def witnessSystemCode {n N : ℕ} {ι : Type*} (d : WitnessSystemData n N ι) :
    Fin 4 × (Fin n → Option (WitnessRelationSlot n N ι)) := by
  classical
  exact (d.mode, fun i => if hi : i ∈ d.chosen then some (d.slot ⟨i, hi⟩) else none)

lemma witnessSystemCode_injective (n N : ℕ) (ι : Type*) :
    Function.Injective (@witnessSystemCode n N ι) := by
  classical
  rintro ⟨mode, chosen, slot⟩ ⟨mode', chosen', slot'⟩ heq
  have hmode : mode = mode' := congrArg Prod.fst heq
  have hfun := congrArg Prod.snd heq
  have hchosen : chosen = chosen' := by
    ext i
    have hi := congrFun hfun i
    by_cases h : i ∈ chosen
    · by_cases h' : i ∈ chosen'
      · exact iff_of_true h h'
      · exfalso
        simp [witnessSystemCode, h, h'] at hi
    · by_cases h' : i ∈ chosen'
      · exfalso
        simp [witnessSystemCode, h, h'] at hi
      · exact iff_of_false h h'
  subst mode'
  subst chosen'
  congr 1
  funext i
  have hi := congrFun hfun i.val
  simpa [witnessSystemCode, i.property] using hi

instance (n N : ℕ) (ι : Type*) [Finite ι] : Finite (WitnessSystemData n N ι) :=
  Finite.of_injective _ (witnessSystemCode_injective n N ι)

noncomputable instance (n N : ℕ) (ι : Type*) [Fintype ι] :
    Fintype (WitnessSystemData n N ι) := Fintype.ofFinite _

lemma card_witnessRelationSlot (n N : ℕ) (ι : Type*) [Fintype ι] :
    Fintype.card (WitnessRelationSlot n N ι) = Fintype.card ι ^ 2 * n * (N + 1) ^ 4 := by
  simp only [WitnessRelationSlot, Fintype.card_prod, Fintype.card_fin]
  ring

/-- A single optional-slot function records the chosen set as well as all
its data, so no extra subset-count factor is needed. -/
theorem card_witnessSystemData_le (n N : ℕ) (ι : Type*) [Fintype ι] :
    Fintype.card (WitnessSystemData n N ι) ≤
      4 * (1 + Fintype.card ι ^ 2 * n * (N + 1) ^ 4) ^ n := by
  have hc := Fintype.card_le_of_injective (@witnessSystemCode n N ι)
    (witnessSystemCode_injective n N ι)
  have heq : Fintype.card (Fin 4 × (Fin n → Option (WitnessRelationSlot n N ι))) =
      4 * (1 + Fintype.card ι ^ 2 * n * (N + 1) ^ 4) ^ n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_option, card_witnessRelationSlot, Nat.add_comm]
  rw [heq] at hc
  exact hc

end TwoPointCorrelations

end OAI

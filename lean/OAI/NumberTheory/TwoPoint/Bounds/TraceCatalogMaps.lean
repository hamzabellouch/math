import OAI.NumberTheory.TwoPoint.Walks.TupleWordPrimeSupport
import OAI.NumberTheory.TwoPoint.Walks.ManyUnlitNumericalWords

namespace OAI

/-! Injective encodings of the same trace catalog.  Numerical-word estimates
and column-wise forest estimates therefore have identical multiplicities. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def columnNatCode {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (a : ColumnPrimeAssignment J R P × (Fin R → Q)) :
    ColumnPrimeAssignment J R P × (Fin R → ℕ) :=
  (a.1, fun i => (a.2 i).val)

lemma columnNatCode_injective {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ} :
    Function.Injective (columnNatCode (P := P) (Q := Q) (R := R)) := by
  intro a b hab
  dsimp only [columnNatCode] at hab
  apply Prod.ext
  · exact congrArg (@Prod.fst (ColumnPrimeAssignment J R P) (Fin R → ℕ)) hab
  · funext i
    exact Subtype.ext (congrFun
      (congrArg (@Prod.snd (ColumnPrimeAssignment J R P) (Fin R → ℕ)) hab) i)

def columnStepCode {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (forward : Fin R → Bool) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) :
    Fin R → SignedStep :=
  fun i => ⟨forward i, columnTuple a.1 i, (a.2 i).val⟩

lemma columnStepCode_word {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (forward : Fin R → Bool) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) :
    List.ofFn (columnStepCode forward a) =
      columnTupleWord a.1 forward (fun i => (a.2 i).val) := rfl

lemma columnStepCode_injective {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (forward : Fin R → Bool) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (columnStepCode (P := P) (Q := Q) forward) := by
  intro a b hab
  apply columnNatCode_injective
  apply columnTupleWord_injective forward hprime hdisjoint
  exact congrArg List.ofFn hab

lemma largeUnlitCatalog_sum {R J : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Finset (Fin R → SignedStep))
    (label : (Fin R → SignedStep) → Fin R × Fin J → ι) (L : ℝ) (hL : 0 ≤ L)
    (term : (Fin R → SignedStep) → Finset (Fin R × Fin J) → ℝ) :
    (∑ a ∈ largeUnlitCatalog F label L, term a.1 a.2) =
      ∑ w ∈ F, ∑ U ∈ (nonsingletonSlots (label w)).powerset.filter
        (fun U => ⌊L ^ (1 / 50 : ℝ)⌋₊ < U.card), term w U := by
  rw [largeUnlitCatalog, sum_sigma]
  apply sum_congr rfl
  intro w _
  apply sum_congr
  · ext U
    simp only [mem_filter, Nat.floor_lt (Real.rpow_nonneg hL _)]
  · intro U _
    rfl

lemma trace_sum_image {α β : Type*} (F : Finset α) (encode : α → β)
    (hinj : Function.Injective encode) (decode : β → α)
    (hdecode : ∀ a ∈ F, decode (encode a) = a) (term : α → ℝ) :
    (∑ b ∈ F.image encode, term (decode b)) = ∑ a ∈ F, term a := by
  rw [sum_image (fun _ _ _ _ h => hinj h)]
  apply sum_congr rfl
  intro a ha
  rw [hdecode a ha]

end TwoPointCorrelations

end OAI

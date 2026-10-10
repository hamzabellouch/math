import OAI.LinearAlgebra.MatrixMultiplication.Completion.Scripts
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionPartitions

open MatrixMultiplication.Foundation RecursiveCompletion
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type*} [Fintype X]

def activeCount (S : FlaggedTensor X Y Z) : ℕ := Fintype.card {x // S.flagB x}
def inactiveCount (S : FlaggedTensor X Y Z) : ℕ := Fintype.card {x // ¬ S.flagB x}

theorem partition_count (S : FlaggedTensor X Y Z) :
    activeCount S + inactiveCount S = Fintype.card X := by
  rw [activeCount, inactiveCount, Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le S.flagB)

theorem card_all (p : X → Prop) (m : ℕ) :
    Fintype.card {x : Fin m → X // ∀ i, p (x i)} = Fintype.card {x // p x} ^ m := by
  calc
    _ = Fintype.card (Fin m → {x // p x}) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = _ := by simp

theorem activeCount_minus (S : FlaggedTensor X Y Z) (m : ℕ) :
    activeCount (complete S .B m) = activeCount S ^ m := by
  simpa [activeCount, complete, flagB, raisedFlag] using card_all S.flagB m

theorem inactiveCount_plus (S : FlaggedTensor X Y Z) (center : Color)
    (hc : center ≠ .B) (m : ℕ) :
    inactiveCount (complete S center m) = inactiveCount S ^ m := by
  change Fintype.card {x : Fin m → X // ¬ raisedFlag center .B (fun i => S.flagB (x i))} = _
  calc
    _ = Fintype.card {x : Fin m → X // ∀ i, ¬ S.flagB (x i)} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x => by simp [raisedFlag, hc])
    _ = Fintype.card (Fin m → {x // ¬ S.flagB x}) :=
      Fintype.card_congr
        { toFun := fun w i => ⟨w.val i, w.property i⟩
          invFun := fun w => ⟨fun i => (w i).val, fun i => (w i).property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    _ = _ := by simp [inactiveCount]

def activeFraction (S : FlaggedTensor X Y Z) : ℝ :=
  (activeCount S : ℝ) / Fintype.card X

def inactiveFraction (S : FlaggedTensor X Y Z) : ℝ :=
  (inactiveCount S : ℝ) / Fintype.card X

theorem fraction_sum [Nonempty X] (S : FlaggedTensor X Y Z) :
    activeFraction S + inactiveFraction S = 1 := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  rw [activeFraction, inactiveFraction, ← add_div, ← Nat.cast_add, partition_count]
  exact div_self hc

theorem activeFraction_minus (S : FlaggedTensor X Y Z) (m : ℕ) :
    activeFraction (complete S .B m) = activeFraction S ^ m := by
  simp only [activeFraction, activeCount_minus, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, div_pow]

theorem inactiveFraction_plus (S : FlaggedTensor X Y Z) (center : Color)
    (hc : center ≠ .B) (m : ℕ) :
    inactiveFraction (complete S center m) = inactiveFraction S ^ m := by
  simp only [inactiveFraction, inactiveCount_plus S center hc m,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_pow]

theorem activeFraction_plus [Nonempty X] (S : FlaggedTensor X Y Z)
    (center : Color) (hc : center ≠ .B) (m : ℕ) :
    activeFraction (complete S center m) = 1 - (1 - activeFraction S) ^ m := by
  have h := fraction_sum (complete S center m)
  rw [inactiveFraction_plus S center hc m] at h
  have hold : inactiveFraction S = 1 - activeFraction S := by
    linarith [fraction_sum S]
  rw [hold] at h
  linarith

end MatrixMultiplication.CompletionPartitions

end

end OAI

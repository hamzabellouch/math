import OAI.Combinatorics.EditApproximation.Binary.BinaryActualBandOptimizer
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadComposition
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The dyadic child envelope explicitly gathers its initial-value
words before taking the maximum. -/

namespace EditApproximation

theorem vectorMapWithWork_extra {α : Type*} (d : ℕ) (read plain : Fin d → α × ℕ) (C : ℕ)
    (hv : ∀ i, (read i).1 = (plain i).1) (hc : ∀ i, (read i).2 ≤ (plain i).2 + C) :
    (vectorMapWithWork d read).1 = (vectorMapWithWork d plain).1 ∧
    (vectorMapWithWork d read).2 ≤ (vectorMapWithWork d plain).2 + d * C := by
  constructor
  · apply Vector.ext
    intro i hi
    change (vectorMapWithWork d read).1.get ⟨i, hi⟩ = (vectorMapWithWork d plain).1.get ⟨i, hi⟩
    rw [vectorMapWithWork_value, vectorMapWithWork_value]
    exact hv _
  · simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
      List.map_ofFn, Function.comp_def, List.sum_ofFn]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hc i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h
    exact (Nat.add_le_add_right h (6 * d)).trans_eq (Nat.add_right_comm _ _ _)

namespace BinaryFraction



theorem bandEnvelopeReadWithWork_eq {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (i : Fin M) :
    (bandEnvelopeReadWithWork b band read i).1 =
      (bandEnvelopeWithWork b band (fun j q => (read j q).1) i).1 := by
  simp only [bandEnvelopeReadWithWork, bandEnvelopeWithWork, arithmeticMapWithWork_value]

theorem bandEnvelopeReadWithWork_cost {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (i : Fin M) (R : ℕ)
    (hr : ∀ action ∈ band, (read i (action i)).2 ≤ R) :
    (bandEnvelopeReadWithWork b band read i).2 ≤
      (bandEnvelopeWithWork b band (fun j q => (read j q).1) i).2 + band.length * (R + 3) := by
  have h := arithmeticMapWithWork_cost (fun action => read i (action i)) band R hr
  simp only [bandEnvelopeReadWithWork, bandEnvelopeWithWork, arithmeticMapWithWork_value]
  omega



theorem envelopeVectorReadWithWork_eq_cost {M n : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval n)) (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (R : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) :
    (envelopeVectorReadWithWork b band read).1 =
      (envelopeVectorWithWork b band (fun i q => (read i q).1)).1 ∧
    (envelopeVectorReadWithWork b band read).2 ≤
      (envelopeVectorWithWork b band (fun i q => (read i q).1)).2 + M * (band.length * (R + 3)) := by
  exact vectorMapWithWork_extra M _ _ _
    (bandEnvelopeReadWithWork_eq b band read)
    (fun i => bandEnvelopeReadWithWork_cost b band read i R (fun _ _ => hr i _))

end BinaryFraction
end EditApproximation

end OAI

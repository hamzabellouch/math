import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedCompare
import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryWeight

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseIndexSpan {B : ℕ} (width : Fin B → ℕ) : List (Fin B) → ℕ
  | [] => 0
  | i :: rest => width i + coarseIndexSpan width rest

def coarseIndexWeight {B : ℕ} (q L : ℕ) (draw : Fin B → Fin B)
    (weight : Fin B → BinaryFraction → ℕ) (allowance : BinaryFraction) : List (Fin B) → ℕ
  | [] => 0
  | i :: rest => weight i (coarseChildAllowanceWithWork L
      (coarseChildThresholdWithWork B q allowance (draw i)).1).1 +
      coarseIndexWeight q L draw weight allowance rest

theorem coarseIndexSpan_eq {B d : ℕ} {α : Type*} (width : Fin B → ℕ)
    (children : Fin B → CoarseSourceTree B α d) (draw : Fin B → Fin B)
    (below : Fin B → CoarseThresholdDraws B d) (hw : ∀ i, width i = (children i).word.length)
    (indices : List (Fin B)) :
    coarseIndexSpan width indices =
      coarseChildrenSpan (indices.map fun i => (children i, draw i, below i)) := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [coarseIndexSpan, List.map_cons, coarseChildrenSpan, hw, ih]

theorem coarseIndexWeight_eq {B d : ℕ} {α : Type*} (k q L : ℕ)
    (children : Fin B → CoarseSourceTree B α d) (draw : Fin B → Fin B)
    (below : Fin B → CoarseThresholdDraws B d) (allowance : BinaryFraction) (indices : List (Fin B)) :
    coarseIndexWeight q L draw (fun i => coarseBinaryWeight k q L (children i) (below i)) allowance indices =
      coarseBinaryChildrenWeight q L (fun child => coarseBinaryWeight k q L child) allowance
        (indices.map fun i => (children i, draw i, below i)) := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [coarseIndexWeight, List.map_cons, coarseBinaryChildrenWeight, ih]

theorem coarseIndexAdditionalWork_bound {B : ℕ} (q L N C K : ℕ)
    (width : Fin B → ℕ) (draw : Fin B → Fin B)
    (extra : Fin B → BinaryFraction → ℕ → ℕ) (weight : Fin B → BinaryFraction → ℕ)
    (allowance : BinaryFraction) (indices : List (Fin B))
    (hc : ∀ i ∈ indices, ∀ s, s + width i ≤ N →
      extra i (coarseChildAllowanceWithWork L
        (coarseChildThresholdWithWork B q allowance (draw i)).1).1 s ≤
        C * weight i (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance (draw i)).1).1 + K)
    (start : ℕ) (hstart : start + coarseIndexSpan width indices ≤ N) :
    coarseIndexAdditionalWork q L width draw extra allowance indices start ≤
      C * coarseIndexWeight q L draw weight allowance indices + K * indices.length := by
  induction indices generalizing start with
  | nil => simp only [coarseIndexAdditionalWork, coarseIndexWeight, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons i rest ih =>
    have hs : start + (width i + coarseIndexSpan width rest) ≤ N := hstart
    have hi := hc i List.mem_cons_self start (by omega)
    have hr := ih (fun j hj => hc j (List.mem_cons_of_mem i hj)) (start + width i) (by omega)
    simp only [coarseIndexAdditionalWork, coarseIndexWeight, List.length_cons,
      Nat.mul_add, Nat.mul_one]
    omega

end BinaryFraction
end EditApproximation

end OAI

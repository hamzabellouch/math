import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedChildren

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseIndexAdditionalWork {B : ℕ} (q L : ℕ) (width : Fin B → ℕ) (draw : Fin B → Fin B)
    (extra : Fin B → BinaryFraction → ℕ → ℕ) (allowance : BinaryFraction) :
    List (Fin B) → ℕ → ℕ
  | [], _ => 0
  | i :: rest, start =>
    extra i (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance (draw i)).1).1 start +
      coarseIndexAdditionalWork q L width draw extra allowance rest (start + width i)

/-- Local arithmetic depends only on returned arrays, so replacing a child
by a representation-equivalent implementation preserves every parent array. -/
theorem coarseIndexChildren_value_congr {B : ℕ} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ) (draw : Fin B → Fin B)
    (evaluate other : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (he : ∀ i a start, (evaluate i a start).1 = (other i a start).1)
    (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    (coarseIndexChildren k q L two width evaluate draw allowance indices start).1 =
      (coarseIndexChildren k q L two width other draw allowance indices start).1 := by
  induction indices generalizing start with
  | nil => rfl
  | cons i rest ih => simp only [coarseIndexChildren, he, ih]


/-- Extra costs compose along the same child traversal; no child arithmetic
or array allocation is charged twice by this comparison. -/
theorem coarseIndexChildren_cost_compare {B : ℕ} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ) (draw : Fin B → Fin B)
    (evaluate other : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (extra : Fin B → BinaryFraction → ℕ → ℕ)
    (he : ∀ i a start, (evaluate i a start).1 = (other i a start).1)
    (hc : ∀ i a start, (evaluate i a start).2 ≤ (other i a start).2 + extra i a start)
    (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    (coarseIndexChildren k q L two width evaluate draw allowance indices start).2 ≤
      (coarseIndexChildren k q L two width other draw allowance indices start).2 +
        coarseIndexAdditionalWork q L width draw extra allowance indices start := by
  induction indices generalizing start with
  | nil => simp only [coarseIndexChildren, coarseIndexAdditionalWork, Nat.add_zero, le_refl]
  | cons i rest ih =>
    let childAllowance := (coarseChildAllowanceWithWork L
      (coarseChildThresholdWithWork B q allowance (draw i)).1).1
    have hi := hc i childAllowance start
    have hr := ih (start + width i)
    have hechild := he i childAllowance start
    have herest := coarseIndexChildren_value_congr k q L two width draw evaluate other he
      allowance rest (start + width i)
    simp only [coarseIndexChildren, coarseIndexAdditionalWork]
    dsimp only [childAllowance] at hi hechild
    rw [hechild, herest]
    omega


theorem arithmeticMapWithWork_add_cost {α β : Type*} (f : α → β × ℕ)
    (extra : α → ℕ) (xs : List α) :
    (arithmeticMapWithWork (fun x => ((f x).1, (f x).2 + extra x)) xs).2 =
      (arithmeticMapWithWork f xs).2 + (xs.map extra).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [arithmeticMapWithWork, List.map_cons, List.sum_cons, ih]
    omega

end BinaryFraction
end EditApproximation

end OAI

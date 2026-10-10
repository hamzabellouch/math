import OAI.Combinatorics.EditApproximation.Coarse.CoarsePenaltyArithmetic
import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayEval
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Binary storage operations used by the shared coarse-array recursion.
A missing array is the same zero marker as in the rational specification. -/

namespace EditApproximation
namespace BinaryFraction



def coarseBinaryContents (array : CoarseBinaryArray) : Option (List ℚ) :=
  array.map (List.map value)

def coarseRationalContents {n : ℕ} (array : CoarseStoredArray n) : Option (List ℚ) :=
  array.map Subtype.val



 theorem coarseBinaryPenaltyWithWork_value (two : BinaryFraction) (values : List BinaryFraction)
    (htwo : two.value = 2)
    (hs : ∀ a ∈ values, a.representation.den = two.representation.den) :
    coarseBinaryContents (coarseBinaryPenaltyWithWork two (some values)).1 =
      some (coarsePenaltyTransform (values.map value)) := by
  exact congrArg some (coarseGridPenaltyWithWork_value two values htwo hs)

/-- Both input lists are visited once; the same denominator is retained. -/


 theorem coarseGridZipAddWithWork_value (left right : List BinaryFraction)
    (hden : ∀ a ∈ left, ∀ b ∈ right, a.representation.den = b.representation.den) :
    (coarseGridZipAddWithWork left right).1.map value =
      List.zipWith (· + ·) (left.map value) (right.map value) := by
  induction left generalizing right with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => rfl
    | cons b right =>
      simp only [coarseGridZipAddWithWork, List.map_cons, List.zipWith_cons_cons]
      rw [coarseGridAddWithWork_value a b (hden a List.mem_cons_self b List.mem_cons_self),
        ih right (fun x hx y hy => hden x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))]

 theorem coarseGridZipAddWithWork_cost (left right : List BinaryFraction)
    (B : ℕ) (hl : ∀ a ∈ left, a.width ≤ B) (hr : ∀ a ∈ right, a.width ≤ B) :
    (coarseGridZipAddWithWork left right).2 ≤
      min left.length right.length * (100 * (B + 1) + 3) := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipAddWithWork, List.length_nil, Nat.zero_min, Nat.zero_mul, le_refl]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipAddWithWork, List.length_nil, Nat.min_zero, Nat.zero_mul, le_refl]
    | cons b right =>
      have hh := coarseGridAddWithWork_cost a b B (hl a List.mem_cons_self) (hr b List.mem_cons_self)
      have ht := ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb))
      change (coarseGridAddWithWork a b).2 + (coarseGridZipAddWithWork left right).2 + 3 ≤ _
      simp only [List.length_cons]
      rw [show min (left.length + 1) (right.length + 1) = min left.length right.length + 1 by omega,
        Nat.add_mul, Nat.one_mul]
      omega





 theorem coarseBinaryMapWithWork_value (f : BinaryFraction → BinaryFraction × ℕ)
    (spec : ℚ → ℚ) (hf : ∀ a, (f a).1.value = spec a.value) (array : CoarseBinaryArray) :
    coarseBinaryContents (coarseBinaryMapWithWork f array).1 =
      (coarseBinaryContents array).map (List.map spec) := by
  cases array with
  | none => rfl
  | some values =>
    simp only [coarseBinaryMapWithWork, coarseBinaryContents, Option.map_some,
      arithmeticMapWithWork_value, List.map_map, Function.comp_def, hf]

end BinaryFraction
end EditApproximation

end OAI

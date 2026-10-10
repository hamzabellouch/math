import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayArithmetic
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction



 theorem coarseGridLeftWithWork_value (two : BinaryFraction) (source : List BinaryFraction)
    (htwo : two.value = 2)
    (hs : ∀ a ∈ source, a.representation.den = two.representation.den) :
    (coarseGridLeftWithWork two source).1.map value = coarseLeftSweep (source.map value) := by
  cases source with
  | nil => rfl
  | cons head rest =>
    exact coarseGridScanWithWork_value two head rest htwo (hs head List.mem_cons_self)
      (fun a ha => hs a (List.mem_cons_of_mem _ ha))

 theorem coarseGridLeftWithWork_bounds (two : BinaryFraction)
    (source : List BinaryFraction) (V D B : ℕ) (htwo : two.value = 2)
    (htw : two.width ≤ B) (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ B)
    (hs : ∀ a ∈ source, CoarseGridCell two a V D B) :
    (∀ a ∈ (coarseGridLeftWithWork two source).1, CoarseGridCell two a V D B) ∧
      (coarseGridLeftWithWork two source).2 ≤ source.length * (1200 * (B + 1) ^ 2 + 3) := by
  cases source with
  | nil => simp only [coarseGridLeftWithWork, List.not_mem_nil, false_implies,
      implies_true, List.length_nil, Nat.zero_mul, le_refl, and_self]
  | cons head rest =>
    have h := coarseGridScanWithWork_bounds two head rest V D B htwo htw hbound
      (hs head List.mem_cons_self) (fun a ha => hs a (List.mem_cons_of_mem _ ha))
    refine ⟨h.1, h.2.trans ?_⟩
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega



 theorem coarseGridZipMinimumWithWork_value (left right : List BinaryFraction) :
    (coarseGridZipMinimumWithWork left right).1.map value =
      List.zipWith min (left.map value) (right.map value) := by
  induction left generalizing right with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => rfl
    | cons b right =>
      simp only [coarseGridZipMinimumWithWork, List.map_cons, List.zipWith_cons_cons,
        minWithWork_value, ih]

 theorem coarseGridZipMinimumWithWork_cost (left right : List BinaryFraction)
    (B : ℕ) (hl : ∀ a ∈ left, a.width ≤ B) (hr : ∀ a ∈ right, a.width ≤ B) :
    (coarseGridZipMinimumWithWork left right).2 ≤
      min left.length right.length * (1000 * (B + 1) ^ 2 + 4) := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipMinimumWithWork, List.length_nil, Nat.zero_min, Nat.zero_mul, le_refl]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipMinimumWithWork, List.length_nil, Nat.min_zero, Nat.zero_mul, le_refl]
    | cons b right =>
      have hh := minWithWork_cost a b B (hl a List.mem_cons_self) (hr b List.mem_cons_self)
      have ht := ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb))
      change (minWithWork a b).2 + (coarseGridZipMinimumWithWork left right).2 + 3 ≤ _
      simp only [List.length_cons]
      rw [show min (left.length + 1) (right.length + 1) = min left.length right.length + 1 by omega,
        Nat.add_mul, Nat.one_mul]
      omega

/-- The two sweeps and final comparison, with every list pass charged. -/


 theorem coarseGridPenaltyWithWork_value (two : BinaryFraction) (source : List BinaryFraction)
    (htwo : two.value = 2)
    (hs : ∀ a ∈ source, a.representation.den = two.representation.den) :
    (coarseGridPenaltyWithWork two source).1.map value = coarsePenaltyTransform (source.map value) := by
  have hl := coarseGridLeftWithWork_value two source htwo hs
  have hr := coarseGridLeftWithWork_value two source.reverse htwo
    (fun a ha => hs a (List.mem_reverse.mp ha))
  simp only [List.map_reverse] at hr
  simp only [coarseGridPenaltyWithWork, coarseGridZipMinimumWithWork_value,
    coarsePenaltyTransform, List.map_reverse, hl, hr]

 theorem coarseGridPenaltyWithWork_cost (two : BinaryFraction) (source : List BinaryFraction)
    (V D B : ℕ) (htwo : two.value = 2) (htw : two.width ≤ B)
    (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ B)
    (hs : ∀ a ∈ source, CoarseGridCell two a V D B) :
    (coarseGridPenaltyWithWork two source).2 ≤ source.length * (3500 * (B + 1) ^ 2 + 20) := by
  have hl := coarseGridLeftWithWork_bounds two source V D B htwo htw hbound hs
  have hr := coarseGridLeftWithWork_bounds two source.reverse V D B htwo htw hbound
    (fun a ha => hs a (List.mem_reverse.mp ha))
  have hv := congrArg List.length (coarseGridLeftWithWork_value two source htwo
    (fun a ha => (hs a ha).1))
  simp only [List.length_map, coarseLeftSweep_length] at hv
  have hz := coarseGridZipMinimumWithWork_cost (coarseGridLeftWithWork two source).1
    (coarseGridLeftWithWork two source.reverse).1.reverse B
    (fun a ha => (hl.1 a ha).2.2.2.2)
    (fun a ha => (hr.1 a (List.mem_reverse.mp ha)).2.2.2.2)
  have hm : min (coarseGridLeftWithWork two source).1.length
      (coarseGridLeftWithWork two source.reverse).1.reverse.length ≤ source.length := by
    exact (min_le_left _ _).trans_eq hv
  have hz' := hz.trans (Nat.mul_le_mul_right _ hm)
  simp only [List.length_reverse] at hr
  change (coarseGridLeftWithWork two source).2 + (coarseGridLeftWithWork two source.reverse).2 +
    (coarseGridZipMinimumWithWork (coarseGridLeftWithWork two source).1
      (coarseGridLeftWithWork two source.reverse).1.reverse).2 + 3 * source.length ≤ _
  nlinarith only [hl.2, hr.2, hz', Nat.zero_le (source.length * (B + 1) ^ 2),
    Nat.zero_le source.length]

end BinaryFraction
end EditApproximation

end OAI

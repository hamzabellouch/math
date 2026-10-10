import OAI.Combinatorics.EditApproximation.Coarse.CoarseThresholdArithmetic
import OAI.Combinatorics.EditApproximation.Coarse.CoarseTransforms
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The coarse penalty sweep executed on shared-denominator Boolean cells.
Each transition performs a numerator addition and a rational comparison. -/

namespace EditApproximation
namespace BinaryFraction

private theorem coarseMin_den (a b : BinaryFraction)
    (hden : a.representation.den = b.representation.den) :
    (minWithWork a b).1.representation.den = a.representation.den := by
  unfold minWithWork
  dsimp only
  split_ifs
  · rfl
  · exact hden.symm

private theorem coarseMin_den_length (a b : BinaryFraction) (D : ℕ)
    (ha : a.denominator.length ≤ D) (hb : b.denominator.length ≤ D) :
    (minWithWork a b).1.denominator.length ≤ D := by
  unfold minWithWork
  dsimp only
  split_ifs <;> assumption

private theorem coarseGridAdd_den_length (a b : BinaryFraction) :
    (coarseGridAddWithWork a b).1.denominator.length ≤ a.denominator.length := by
  change (trimBitWordWithWork a.denominator).1.length ≤ a.denominator.length
  rw [trimBitWordWithWork_length]
  exact Nat.size_le.mpr (bitWordValue_lt_pow_length _)

/-- The complete left sweep, including writes and traversal. -/


 theorem coarseGridScanWithWork_value (two previous : BinaryFraction)
    (source : List BinaryFraction) (htwo : two.value = 2)
    (hp : previous.representation.den = two.representation.den)
    (hs : ∀ a ∈ source, a.representation.den = two.representation.den) :
    (coarseGridScanWithWork two previous source).1.map value =
      (source.map value).scanl (fun old a => min a (old + 2)) previous.value := by
  induction source generalizing previous with
  | nil => rfl
  | cons head rest ih =>
    have hh := hs head List.mem_cons_self
    have ha : (coarseGridAddWithWork previous two).1.representation.den = two.representation.den :=
      (coarseGridAddWithWork_den previous two).trans hp
    have hn : (minWithWork head (coarseGridAddWithWork previous two).1).1.representation.den =
        two.representation.den :=
      (coarseMin_den head _ (hh.trans ha.symm)).trans hh
    have hv := coarseGridAddWithWork_value previous two hp
    simp only [coarseGridScanWithWork, List.map_cons, List.scanl_cons]
    rw [ih _ hn (fun a ha => hs a (List.mem_cons_of_mem _ ha)), minWithWork_value, hv, htwo]

/-- Invariant of a stored coarse cell on the common denominator. -/
def CoarseGridCell (two a : BinaryFraction) (V D B : ℕ) : Prop :=
  a.representation.den = two.representation.den ∧ a.denominator.length ≤ D ∧
    0 ≤ a.value ∧ a.value ≤ V ∧ a.width ≤ B

 theorem coarseGridScanWithWork_bounds (two previous : BinaryFraction)
    (source : List BinaryFraction) (V D B : ℕ) (htwo : two.value = 2)
    (htw : two.width ≤ B) (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ B)
    (hp : CoarseGridCell two previous V D B)
    (hs : ∀ a ∈ source, CoarseGridCell two a V D B) :
    (∀ a ∈ (coarseGridScanWithWork two previous source).1, CoarseGridCell two a V D B) ∧
      (coarseGridScanWithWork two previous source).2 ≤
        source.length * (1200 * (B + 1) ^ 2 + 3) := by
  induction source generalizing previous with
  | nil =>
    constructor
    · simpa only [coarseGridScanWithWork, List.mem_singleton] using
        (fun a (ha : a = previous) => ha ▸ hp)
    · simp only [coarseGridScanWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons head rest ih =>
    have hh := hs head List.mem_cons_self
    have hav : |previous.value + two.value| ≤ (V + 2 : ℕ) := by
      rw [htwo, abs_of_nonneg (by linarith only [hp.2.2.1])]
      push_cast
      linarith only [hp.2.2.2.1]
    have haw := (coarseGridAddWithWork_width previous two (V + 2) D hp.1 hav hp.2.1).trans hbound
    have had := (coarseGridAddWithWork_den previous two).trans hp.1
    have hv := coarseGridAddWithWork_value previous two hp.1
    have hn : CoarseGridCell two (minWithWork head (coarseGridAddWithWork previous two).1).1 V D B := by
      refine ⟨(coarseMin_den head _ (hh.1.trans had.symm)).trans hh.1,
        coarseMin_den_length head _ D hh.2.1
          ((coarseGridAdd_den_length previous two).trans hp.2.1), ?_, ?_, ?_⟩
      · rw [minWithWork_value, hv, htwo]
        exact le_min hh.2.2.1 (by linarith only [hp.2.2.1])
      · rw [minWithWork_value]
        exact (min_le_left _ _).trans hh.2.2.2.1
      · exact (minWithWork_width head _).trans (max_le hh.2.2.2.2 haw)
    have ht := ih _ hn (fun a ha => hs a (List.mem_cons_of_mem _ ha))
    constructor
    · intro a ha
      change a ∈ previous :: _ at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hp
      · exact ht.1 a ha
    · have hc := coarseGridAddWithWork_cost previous two B hp.2.2.2.2 htw
      have hm := minWithWork_cost head _ B hh.2.2.2.2 haw
      change (coarseGridAddWithWork previous two).2 +
        (minWithWork head (coarseGridAddWithWork previous two).1).2 +
        (coarseGridScanWithWork two (minWithWork head (coarseGridAddWithWork previous two).1).1 rest).2 + 3 ≤ _
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      nlinarith only [hc, hm, ht.2, Nat.zero_le B]

end BinaryFraction
end EditApproximation

end OAI

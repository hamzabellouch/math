import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialWorkBounds

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- The dyadic wrapper adds only comparisons, a scan, ceiling, and clamp
beyond the sum of the actually executed candidate counters. -/
theorem coarseInitialWithWork_cost {B d : ℕ} (q L N A S : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d)
    (hA : 2 ≤ A) (hN : Nat.size N ≤ A)
    (hx : Nat.size x.length ≤ A) (hy : Nat.size y.length ≤ A)
    (hs : ∀ a ∈ x ++ y, Nat.size a ≤ S)
    (hc : ∀ i, (coarseCandidateWithWork q L hB hq hL x y i (draws i)).1.width ≤ A) :
    (coarseInitialWithWork q L N hB hq hL x y draws).2 ≤
      ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map
        (fun i => (coarseCandidateWithWork q L hB hq hL x y i (draws i)).2)).sum +
      (x.length + y.length + 1) * (8 * S + 4) +
      10000 * (Nat.clog 2 (coarseEntryWidth x y) + 2) * (A + 2) ^ 2 := by
  let f := fun i => coarseCandidateWithWork q L hB hq hL x y i (draws i)
  let indices := List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)
  let roots := arithmeticMapWithWork f indices
  have hl := binaryNaturalCompareWithWork_cost (2 * x.length) y.length
  have hxl := natural_product_bit_length 2 x.length
  rw [show Nat.size 2 = 2 by decide] at hxl
  have hlong : (binaryNaturalCompareWithWork (2 * x.length) y.length).2 ≤ 8 * A + 9 := by omega
  have hequal := naturalListEqualWithWork_cost x y S hs
  have hw : ∀ a ∈ roots.1, a.width ≤ A := by
    intro a ha
    rw [arithmeticMapWithWork_value] at ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact hc i
  have hm := coarseMinimumWithWork_bounds roots.1 A hA hw
  have hlen : roots.1.length = Nat.clog 2 (coarseEntryWidth x y) + 1 := by
    simp only [roots, arithmeticMapWithWork_value, List.length_map, indices, List.length_finRange]
  rw [hlen] at hm
  have hr := naturalCeilingWithWork_cost (coarseMinimumWithWork roots.1).1
  have hrw := naturalCeilingWithWork_length (coarseMinimumWithWork roots.1).1
  have hr' : (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).2 ≤ 500 * (A + 1) ^ 2 :=
    hr.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 2))
  have hcmp := wordLEWithWork_cost N.bits (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1
  rw [Nat.size_eq_bits_len] at hcmp
  have hclamp : (wordMinWithWork N.bits (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1).2 ≤
      8 * A + 11 := by
    change (wordLEWithWork _ _).2 + 1 ≤ _
    omega
  have hmap := arithmeticMapWithWork_total f indices
  change roots.2 = _ at hmap
  have hmap' : roots.2 = (indices.map (fun i => (f i).2)).sum +
      3 * (Nat.clog 2 (coarseEntryWidth x y) + 1) := by
    simpa only [indices, List.length_finRange] using hmap
  change _ ≤ (indices.map (fun i => (f i).2)).sum + _ + _
  unfold coarseInitialWithWork
  dsimp only
  split_ifs
  · dsimp only
    nlinarith only [hlong, hA, hN, hy,
      Nat.zero_le ((indices.map (fun i => (f i).2)).sum),
      Nat.zero_le ((x.length + y.length + 1) * (8 * S + 4)),
      Nat.zero_le (Nat.clog 2 (coarseEntryWidth x y))]
  · dsimp only
    nlinarith only [hlong, hequal, hA,
      Nat.zero_le ((indices.map (fun i => (f i).2)).sum),
      Nat.zero_le (Nat.clog 2 (coarseEntryWidth x y))]
  · change _ + _ + roots.2 + (coarseMinimumWithWork roots.1).2 +
      (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).2 +
      (wordMinWithWork N.bits (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1).2 +
      Nat.size N + 6 ≤ _
    rw [hmap']
    nlinarith only [hlong, hequal, hm.2, hr', hclamp, hA, hN,
      Nat.zero_le (Nat.clog 2 (coarseEntryWidth x y))]

end BinaryFraction
end EditApproximation

end OAI

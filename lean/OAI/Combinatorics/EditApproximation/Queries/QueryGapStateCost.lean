import OAI.Combinatorics.EditApproximation.Queries.QuerySharedGeometry
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryBounds

namespace OAI

namespace EditApproximation

theorem gridPointsBetween_radius_count (g p radius : ℕ) (hg : 0 < g) :
    (gridPointsBetween g (p - radius) (p + radius)).length ≤ 2 * radius / g + 2 :=
  (gridPointsBetween_length_le g _ _ hg).trans
    (Nat.add_le_add_right (Nat.div_le_div_right (by omega : p + radius - (p - radius) ≤ 2 * radius)) 2)

def queryGapStatesBitBudget (left right B : ℕ) : ℕ :=
  let C := 1000 * (B + 10) ^ 2
  C + gridPointsBitBudget left (B + 2) +
    left * (C + gridPointsBitBudget right (B + 6) + right * (16 * (B + 6) + 11) + right + 7) + 3

private theorem queryGapStates_arithmetic_bound (B u v w : ℕ)
    (hu : u ≤ 26 * (B + 4) + 4) (hv : v ≤ 26 * (B + 4) + 4)
    (hw : w ≤ 26 * (B + 4) + 4) :
    u + v + w ≤ 1000 * (B + 10) ^ 2 := by
  nlinarith only [hu, hv, hw, Nat.zero_le B]

theorem queryGapStatesWithWork_bounds (n g anchor radius sourceLength gapRadius left right B : ℕ)
    (hg : 0 < g) (hn : Nat.size n ≤ B) (hgs : Nat.size g ≤ B)
    (ha : Nat.size anchor ≤ B) (hr : Nat.size radius ≤ B)
    (hl : Nat.size sourceLength ≤ B) (hgap : Nat.size gapRadius ≤ B)
    (hleft : 2 * radius / g + 2 ≤ left) (hright : 2 * gapRadius / g + 2 ≤ right) :
    (queryGapStatesWithWork n g anchor radius sourceLength gapRadius).1.length ≤ left * right ∧
    (queryGapStatesWithWork n g anchor radius sourceLength gapRadius).2 ≤
      queryGapStatesBitBudget left right B := by
  let lo := saturatingSubtractWithWork anchor radius
  let hi := binaryNaturalAddWithWork anchor radius
  let firsts := gridPointsWithWork g (bitWordValue lo.1) (bitWordValue hi.1)
  let run := fun first =>
    let center := binaryNaturalAddWithWork first sourceLength
    let lower := saturatingSubtractWithWork (bitWordValue center.1) gapRadius
    let upper := binaryNaturalAddWithWork (bitWordValue center.1) gapRadius
    let last := gridPointsWithWork g (bitWordValue lower.1) (bitWordValue upper.1)
    let valid := filterMapWithWork (makeStateWithWork n first) last.1
    (valid.1, center.2 + lower.2 + upper.2 + last.2 + valid.2 + 4)
  let C := 1000 * (B + 10) ^ 2
  have hv : firsts.1 = gridPointsBetween g (anchor - radius) (anchor + radius) := by
    simp only [firsts, gridPointsWithWork_value _ _ _ hg, lo, hi,
      saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
  have hflen : firsts.1.length ≤ left := by rw [hv]; exact (gridPointsBetween_radius_count g anchor radius hg).trans hleft
  have hlow : Nat.size (bitWordValue lo.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans ha
  have hhigh : Nat.size (bitWordValue hi.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le anchor radius).trans (by omega)
  have hfc := gridPointsWithWork_cost g (bitWordValue lo.1) (bitWordValue hi.1) (B + 2) hg
    (by omega) (by omega) hhigh
  rw [← gridPointsWithWork_value g (bitWordValue lo.1) (bitWordValue hi.1) hg] at hfc
  have hfc' : firsts.2 ≤ gridPointsBitBudget left (B + 2) := hfc.trans (by
    unfold gridPointsBitBudget
    gcongr)
  have hfirst (first : ℕ) (hf : first ∈ firsts.1) : Nat.size first ≤ B + 2 := by
    rw [hv] at hf
    exact (Nat.size_le_size (gridPointsBetween_sound hg hf).2.1).trans
      ((binaryNaturalAdd_size_le anchor radius).trans (by omega))
  have hrun (first : ℕ) (hf : first ∈ firsts.1) :
      (run first).1.length ≤ right ∧
      (run first).2 ≤ C + gridPointsBitBudget right (B + 6) + right * (16 * (B + 6) + 11) + 4 := by
    let center := binaryNaturalAddWithWork first sourceLength
    let lower := saturatingSubtractWithWork (bitWordValue center.1) gapRadius
    let upper := binaryNaturalAddWithWork (bitWordValue center.1) gapRadius
    let last := gridPointsWithWork g (bitWordValue lower.1) (bitWordValue upper.1)
    have hsfirst := hfirst first hf
    have hcenter : Nat.size (bitWordValue center.1) ≤ B + 4 := by
      rw [binaryNaturalAddWithWork_value]
      exact (binaryNaturalAdd_size_le first sourceLength).trans (by omega)
    have hslow : Nat.size (bitWordValue lower.1) ≤ B + 4 := by
      rw [saturatingSubtractWithWork_value]
      exact (Nat.size_le_size (Nat.sub_le _ _)).trans hcenter
    have hsup : Nat.size (bitWordValue upper.1) ≤ B + 6 := by
      rw [binaryNaturalAddWithWork_value]
      exact (binaryNaturalAdd_size_le (bitWordValue center.1) gapRadius).trans (by omega)
    have hlv : last.1 = gridPointsBetween g (bitWordValue center.1 - gapRadius)
        (bitWordValue center.1 + gapRadius) := by
      simp only [last, gridPointsWithWork_value _ _ _ hg, lower, upper,
        saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value]
    have hllen : last.1.length ≤ right := by
      rw [hlv]
      exact (gridPointsBetween_radius_count g (bitWordValue center.1) gapRadius hg).trans hright
    have hlastCost := gridPointsWithWork_cost g (bitWordValue lower.1)
      (bitWordValue upper.1) (B + 6) hg (by omega) (by omega) hsup
    rw [← gridPointsWithWork_value g (bitWordValue lower.1) (bitWordValue upper.1) hg] at hlastCost
    have hlast : last.2 ≤ gridPointsBitBudget right (B + 6) := by
      have hmono : gridPointsBitBudget last.1.length (B + 6) ≤ gridPointsBitBudget right (B + 6) := by
        unfold gridPointsBitBudget
        gcongr
      have hcost : last.2 ≤ gridPointsBitBudget last.1.length (B + 6) := by
        simpa only [last] using hlastCost
      exact hcost.trans hmono
    have hvalid := (filterMapWithWork_cost (makeStateWithWork n first) last.1
      (16 * (B + 6) + 8) (fun second hsecond =>
        makeStateWithWork_cost n first second (B + 6) (by omega) (by omega) (by
          rw [hlv] at hsecond
          exact (Nat.size_le_size (gridPointsBetween_sound hg hsecond).2.1).trans (by
            simpa only [upper, binaryNaturalAddWithWork_value] using hsup)))).trans
              (Nat.mul_le_mul_right _ hllen)
    have hcc : center.2 ≤ 9 * (Nat.size first + Nat.size sourceLength) + 1 := by
      simpa only [center] using binaryNaturalAddWithWork_cost first sourceLength
    have hlc : lower.2 ≤ 13 * (Nat.size (bitWordValue center.1) + Nat.size gapRadius) + 4 := by
      simpa only [lower] using saturatingSubtractWithWork_cost (bitWordValue center.1) gapRadius
    have huc : upper.2 ≤ 9 * (Nat.size (bitWordValue center.1) + Nat.size gapRadius) + 1 := by
      simpa only [upper] using binaryNaturalAddWithWork_cost (bitWordValue center.1) gapRadius
    have harith : center.2 + lower.2 + upper.2 ≤ C := by
      exact queryGapStates_arithmetic_bound B center.2 lower.2 upper.2
        (hcc.trans (by omega)) (hlc.trans (by omega)) (huc.trans (by omega))
    constructor
    · have hlen : (filterMapWithWork (makeStateWithWork n first) last.1).1.length ≤ right := by
        rw [filterMapWithWork_value]
        exact (List.length_filterMap_le _ _).trans hllen
      simpa only [run, center, lower, upper, last] using hlen
    · have hcost : center.2 + lower.2 + upper.2 + last.2 +
          (filterMapWithWork (makeStateWithWork n first) last.1).2 + 4 ≤
          C + gridPointsBitBudget right (B + 6) + right * (16 * (B + 6) + 11) + 4 := by
        simp only [Nat.add_assoc, Nat.reduceAdd] at hvalid
        omega
      simpa only [run, center, lower, upper, last] using hcost
  have hflat := (arithmeticFlatMapWithWork_cost run firsts.1
    (C + gridPointsBitBudget right (B + 6) + right * (16 * (B + 6) + 11) + 4) right
    (fun first hf => (hrun first hf).2) (fun first hf => (hrun first hf).1)).trans
      (Nat.mul_le_mul_right _ hflen)
  have hlc : lo.2 ≤ 13 * (Nat.size anchor + Nat.size radius) + 4 := by
    simpa only [lo] using saturatingSubtractWithWork_cost anchor radius
  have huc : hi.2 ≤ 9 * (Nat.size anchor + Nat.size radius) + 1 := by
    simpa only [hi] using binaryNaturalAddWithWork_cost anchor radius
  have hsetup : lo.2 + hi.2 ≤ C := by
    have h := queryGapStates_arithmetic_bound B lo.2 hi.2 0
      (hlc.trans (by omega)) (huc.trans (by omega)) (by omega)
    simpa only [Nat.add_zero] using h
  constructor
  · have hlen := (arithmeticFlatMapWithWork_length run firsts.1 right
      (fun first hf => (hrun first hf).1)).trans (Nat.mul_le_mul_right _ hflen)
    simpa only [queryGapStatesWithWork, lo, hi, firsts, run] using hlen
  · have hcost : lo.2 + hi.2 + firsts.2 + (arithmeticFlatMapWithWork run firsts.1).2 + 3 ≤
        queryGapStatesBitBudget left right B := by
      unfold queryGapStatesBitBudget
      change _ ≤ C + gridPointsBitBudget left (B + 2) +
        left * (C + gridPointsBitBudget right (B + 6) + right * (16 * (B + 6) + 11) + right + 7) + 3
      rw [show C + gridPointsBitBudget right (B + 6) + right * (16 * (B + 6) + 11) + 4 + right + 3 =
        C + gridPointsBitBudget right (B + 6) + right * (16 * (B + 6) + 11) + right + 7 by omega] at hflat
      omega
    simpa only [queryGapStatesWithWork, lo, hi, firsts, run] using hcost

end EditApproximation

end OAI

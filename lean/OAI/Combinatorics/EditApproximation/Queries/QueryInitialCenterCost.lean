import OAI.Combinatorics.EditApproximation.Queries.QueryGridCost
import OAI.Combinatorics.EditApproximation.Queries.QueryInitialConeCenters
import OAI.Combinatorics.EditApproximation.Queries.QueryScalarDispatch
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryBounds
import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialGuardWork

namespace OAI

/-! The initial gather pays for all candidate centers, including those
whose eligibility is tested only after their seed value has been read. -/

namespace EditApproximation.BinaryFraction

theorem queryInitialScale_radius (radius b Amax : ℕ) (A : BinaryFraction)
    (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax)
    (hguard : (initialScaleGuardWithWork radius b A).1 = true) :
    radius ≤ (16 * Amax ^ 2) * b := by
  have hw := (initialScaleGuardWithWork_value radius b A).mp hguard
  have hp : 0 < A.value := by linarith
  have hd := (div_le_iff₀ (show (0 : ℚ) < 16 * A.value ^ 2 by positivity)).mp hw.1
  have hs := pow_le_pow_left₀ hp.le hmax 2
  have hm := mul_le_mul_of_nonneg_right hs (show (0 : ℚ) ≤ 16 * b by positivity)
  have h : (radius : ℚ) ≤ ((16 * Amax ^ 2) * b : ℕ) := by
    push_cast
    nlinarith only [hd, hm]
  exact_mod_cast h

def queryInitialCentersBitBudget (P Amax B : ℕ) : ℕ :=
  let L := (64 * Amax ^ 2 * P + 2) ^ 2
  500 * (B + 1) ^ 2 + (B + 1) * (B + 9) + 2 +
    (B + 1) * (initialScaleGuardBitBudget (B + 4) + 3) +
    (B + 1) * (queryGridPointsBitBudget P (16 * Amax ^ 2) (B + 2) + L + 3) + 2

theorem queryInitialConeCentersWithWork_bounds {n : ℕ} (N P Amax B : ℕ)
    (A value : BinaryFraction) (q : TargetInterval n)
    (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hn : Nat.size n ≤ B) (hAb : A.width ≤ B) (hvb : value.width ≤ B)
    (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax) :
    (queryInitialConeCentersWithWork N P A value q).1.length ≤
      (B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2 ∧
    (queryInitialConeCentersWithWork N P A value q).2 ≤ queryInitialCentersBitBudget P Amax B := by
  let radius := naturalCeilingWithWork value
  let scales := dyadicScalesWithWork N
  let guard := fun b => initialScaleGuardWithWork (bitWordValue radius.1) b A
  let active := filterWithWork guard scales.1
  let run := fun b => queryGridPointsWithWork P b (bitWordValue radius.1) q
  let centers := arithmeticFlatMapWithWork run active.1
  let L := (64 * Amax ^ 2 * P + 2) ^ 2
  have hrad : Nat.size (bitWordValue radius.1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans
      ((naturalCeilingWithWork_length value).trans (by omega))
  have hrwork := (naturalCeilingWithWork_cost value).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hvb 1) 2))
  have hsc : scales.1.length ≤ B + 1 := by
    simp only [scales, dyadicScalesWithWork, arithmeticMapWithWork_value, List.length_map, List.length_range,
      Nat.size_eq_bits_len]
    omega
  have hswork : scales.2 ≤ (B + 1) * (B + 9) + 2 :=
    (dyadicScalesWithWork_cost N).trans
      (Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 2)
  have hb (b : ℕ) (hb : b ∈ scales.1) : Nat.size b ≤ B + 1 := by
    rw [dyadicScalesWithWork_value] at hb
    exact (dyadicScales_size_bound N b hb).trans (by omega)
  have hg := filterWithWork_cost guard scales.1 (initialScaleGuardBitBudget (B + 4)) (by
    intro b hmem
    exact initialScaleGuardWithWork_cost _ b (B + 4) A (by omega) (by omega)
      (by have := hb b hmem; omega) (by omega))
  have hgwork : active.2 ≤ (B + 1) * (initialScaleGuardBitBudget (B + 4) + 3) :=
    hg.trans (Nat.mul_le_mul_right _ hsc)
  have hactive : active.1.length ≤ B + 1 := by
    rw [filterWithWork_value]
    exact (List.length_filter_le _ _).trans hsc
  have hrun (b : ℕ) (hmem : b ∈ active.1) :
      (run b).1.length ≤ L ∧
      (run b).2 ≤ queryGridPointsBitBudget P (16 * Amax ^ 2) (B + 2) := by
    rw [filterWithWork_value] at hmem
    obtain ⟨hbmem, hbguard⟩ := List.mem_filter.mp hmem
    have hsize := hb b hbmem
    have hr := queryInitialScale_radius (bitWordValue radius.1) b Amax A hA hmax hbguard
    have h := queryGridPointsWithWork_bounds P b (bitWordValue radius.1) (16 * Amax ^ 2) (B + 2) q
      hP (by omega) (by omega) hrad (by omega) hr
    simpa only [run, L, show 4 * (16 * Amax ^ 2) * P = 64 * Amax ^ 2 * P by ring] using h
  have hl := (arithmeticFlatMapWithWork_length run active.1 L
    (fun b hb => (hrun b hb).1)).trans (Nat.mul_le_mul_right L hactive)
  have hc := (arithmeticFlatMapWithWork_cost run active.1
    (queryGridPointsBitBudget P (16 * Amax ^ 2) (B + 2)) L
    (fun b hb => (hrun b hb).2) (fun b hb => (hrun b hb).1)).trans
      (Nat.mul_le_mul_right _ hactive)
  change centers.2 ≤ _ at hc
  change radius.2 ≤ _ at hrwork
  refine ⟨hl, ?_⟩
  change radius.2 + scales.2 + active.2 + centers.2 + 2 ≤ _
  change _ ≤ 500 * (B + 1) ^ 2 + (B + 1) * (B + 9) + 2 +
    (B + 1) * (initialScaleGuardBitBudget (B + 4) + 3) +
    (B + 1) * (queryGridPointsBitBudget P (16 * Amax ^ 2) (B + 2) + L + 3) + 2
  omega

end EditApproximation.BinaryFraction

end OAI

import OAI.Combinatorics.EditApproximation.Queries.QueryGridCost
import OAI.Combinatorics.EditApproximation.Queries.QueryScalarDispatch
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryBounds
import OAI.Combinatorics.EditApproximation.Queries.QueryOrderBounds

namespace OAI

/-! Complete work of scale enumeration and unfiltered center construction.
Quadratic duplicate removal is bounded by the actual local grid sizes. -/

namespace EditApproximation.BinaryFraction

def queryScalesBitBudget (B : ℕ) : ℕ :=
  queryExponentsBitBudget B + (B + 1) * (B + 6) + 1

theorem queryScalesWithWork_bounds (N F B : ℕ) (a value : BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) :
    (queryScalesWithWork N F a value).1.length ≤ B + 1 ∧
    (queryScalesWithWork N F a value).2 ≤ queryScalesBitBudget B := by
  let exponents := queryExponentsWithWork N F a value
  have he := queryExponentsWithWork_bounds N F B a value hB hN hF ha hv
  have hc := arithmeticMapWithWork_cost (fun e => (bitWordValue (powerTwoWord e), e + 3))
    exponents.1 (B + 3) (by
      intro e he
      change e ∈ (queryExponentsWithWork N F a value).1 at he
      simp only [queryExponentsWithWork, filterWithWork_value] at he
      have hr := List.mem_range.mp (List.mem_filter.mp he).1
      rw [Nat.size_eq_bits_len] at hr
      change e + 3 ≤ B + 3
      omega)
  constructor
  · simpa only [queryScalesWithWork, arithmeticMapWithWork_value, List.length_map] using he.2
  · have hm := hc.trans (Nat.mul_le_mul_right _ he.2)
    change exponents.2 +
      (arithmeticMapWithWork (fun e => (bitWordValue (powerTwoWord e), e + 3)) exponents.1).2 + 1 ≤ _
    dsimp only [queryScalesBitBudget]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hm
    have hex : exponents.2 ≤ queryExponentsBitBudget B := he.1
    omega

theorem queryScalesWithWork_member (N F B : ℕ) (a value : BinaryFraction)
    (hN : Nat.size N ≤ B) (hF : 1 ≤ F) (b : ℕ)
    (hb : b ∈ (queryScalesWithWork N F a value).1) :
    Nat.size b ≤ B + 1 ∧ ⌈value.value⌉₊ ≤ (16 * F) * b := by
  rw [queryScalesWithWork_value] at hb
  obtain ⟨hdyadic, hguard⟩ := List.mem_filter.mp hb
  have hguard' := of_decide_eq_true hguard
  refine ⟨(dyadicScales_size_bound N b hdyadic).trans (by omega), ?_⟩
  apply Nat.ceil_le.mpr
  have hp : (0 : ℚ) < 16 * F := by
    have hf : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
    positivity
  have h := (div_le_iff₀ hp).mp hguard'.1
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using h

def queryRawCentersBitBudget (P F B : ℕ) : ℕ :=
  let L := (64 * F * P + 2) ^ 2
  let count := (B + 1) * L
  queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (queryGridPointsBitBudget P (16 * F) (B + 2) + L + 3) +
    (count + 1) ^ 2 * (16 * B + 9) + 3

theorem queryRawCentersWithWork_bounds {n : ℕ} (N P F B : ℕ)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hP : 0 < P) (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) :
    (queryRawCentersWithWork N P F a value q).1.length ≤ (B + 1) * (64 * F * P + 2) ^ 2 ∧
    (queryRawCentersWithWork N P F a value q).2 ≤ queryRawCentersBitBudget P F B := by
  let scales := queryScalesWithWork N F a value
  let radius := naturalCeilingWithWork value
  let run := fun b => queryGridPointsWithWork P b (bitWordValue radius.1) q
  let centers := arithmeticFlatMapWithWork run scales.1
  let L := (64 * F * P + 2) ^ 2
  let count := (B + 1) * L
  have hs := queryScalesWithWork_bounds N F B a value (by omega) hN hF ha hv
  have hr : Nat.size (bitWordValue radius.1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans
      ((naturalCeilingWithWork_length value).trans (by omega))
  have hrun (b : ℕ) (hb : b ∈ scales.1) :
      (run b).1.length ≤ L ∧ (run b).2 ≤ queryGridPointsBitBudget P (16 * F) (B + 2) := by
    have hm := queryScalesWithWork_member N F B a value hN hFpos b hb
    have hc : bitWordValue radius.1 ≤ (16 * F) * b := by
      rw [naturalCeilingWithWork_value]
      exact hm.2
    have hg := queryGridPointsWithWork_bounds P b (bitWordValue radius.1) (16 * F) (B + 2) q
      hP (by omega) (by omega) hr (by omega) hc
    simpa only [run, L, show 4 * (16 * F) * P = 64 * F * P by ring] using hg
  have hl := arithmeticFlatMapWithWork_length run scales.1 L (fun b hb => (hrun b hb).1)
  have hw := arithmeticFlatMapWithWork_cost run scales.1
    (queryGridPointsBitBudget P (16 * F) (B + 2)) L
    (fun b hb => (hrun b hb).2) (fun b hb => (hrun b hb).1)
  have hl' : centers.1.length ≤ count := hl.trans (Nat.mul_le_mul_right L hs.1)
  have hw' := hw.trans (Nat.mul_le_mul_right _ hs.1)
  change centers.2 ≤ (B + 1) * (queryGridPointsBitBudget P (16 * F) (B + 2) + L + 3) at hw'
  have he := queryEraseWithWork_cost queryIntervalEqualWithWork (16 * B + 5)
    (fun r s => queryIntervalEqualWithWork_cost r s B hn) centers.1
  have he' := he.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.add_le_add_right hl' 1) 2))
  rw [show 16 * B + 5 + 4 = 16 * B + 9 by omega] at he'
  have hu := (queryEraseWithWork_length queryIntervalEqualWithWork centers.1).trans hl'
  have hrad := (naturalCeilingWithWork_cost value).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hv 1) 2))
  refine ⟨hu, ?_⟩
  change scales.2 + radius.2 + centers.2 +
    (queryEraseWithWork queryIntervalEqualWithWork centers.1).2 + 3 ≤ _
  change _ ≤ queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (queryGridPointsBitBudget P (16 * F) (B + 2) + L + 3) +
    (count + 1) ^ 2 * (16 * B + 9) + 3
  have hsc : scales.2 ≤ queryScalesBitBudget B := hs.2
  change radius.2 ≤ _ at hrad
  omega

end EditApproximation.BinaryFraction

end OAI

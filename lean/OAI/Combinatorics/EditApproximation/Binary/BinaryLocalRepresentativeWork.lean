import OAI.Combinatorics.EditApproximation.Binary.BinaryRefinementLists
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGuardWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryWideChildWork
import OAI.Combinatorics.EditApproximation.Geometry.InitialInputBudget

namespace OAI

/-! Complete bit work of the query-local scale and center loops. The
one-dimensional grid size follows from the tested scale inequality. -/

namespace EditApproximation
namespace BinaryFraction

def queryExponentsBitBudget (B : ℕ) : ℕ :=
  (B + 1) * (localEligibilityBitBudget (B + 4) + B + 5) + 2 * B + 3

theorem queryExponentsWithWork_bounds (N F B : ℕ) (a w : BinaryFraction)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hw : w.width ≤ B) :
    (queryExponentsWithWork N F a w).2 ≤ queryExponentsBitBudget B ∧
      (queryExponentsWithWork N F a w).1.length ≤ B + 1 := by
  let count := max 1 N.bits.length
  have hc : count ≤ B + 1 := by
    dsimp only [count]
    rw [Nat.size_eq_bits_len]
    omega
  have hcost := filterWithWork_cost (fun e =>
    let guard := refinementScaleGuardWithWork F (2 ^ e) a w
    (guard.1, guard.2 + e + 2)) (List.range count)
    (localEligibilityBitBudget (B + 4) + B + 2) (by
      intro e he
      have he' := List.mem_range.mp he
      have hpow : Nat.size (2 ^ e) + 2 ≤ B + 4 := by
        rw [Nat.size_pow]
        omega
      have h := refinementScaleGuardWithWork_cost F (2 ^ e) (B + 4) a w
        (by omega) hpow (by omega) (by omega) (by omega)
      change (refinementScaleGuardWithWork F (2 ^ e) a w).2 + e + 2 ≤ _
      omega)
  simp only [List.length_range] at hcost
  have hlen : (filterWithWork (fun e =>
      let guard := refinementScaleGuardWithWork F (2 ^ e) a w
      (guard.1, guard.2 + e + 2)) (List.range count)).1.length ≤ count := by
    rw [filterWithWork_value]
    exact (List.length_filter_le _ _).trans_eq (List.length_range)
  constructor
  · have hcost' := hcost.trans (Nat.mul_le_mul_right _ hc)
    change (filterWithWork (fun e => ((refinementScaleGuardWithWork F (2 ^ e) a w).1,
      (refinementScaleGuardWithWork F (2 ^ e) a w).2 + e + 2)) (List.range count)).2 +
      count + N.bits.length + 2 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hcost'
    unfold queryExponentsBitBudget
    rw [Nat.size_eq_bits_len]
    simp only [Nat.add_assoc] at hcost' ⊢
    omega
  · exact hlen.trans hc

private theorem query_grid_count (P b radius F : ℕ) (hP : 0 < P)
    (hr : radius ≤ 16 * F * b) :
    2 * radius / seedGridSpacing b P + 2 ≤ 64 * F * P + 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hq : b / P ≤ seedGridSpacing b P := le_max_right _ _
  have hdiv := Nat.lt_mul_div_succ b hP
  have hb : b ≤ 2 * P * seedGridSpacing b P := by nlinarith only [hq, hdiv, hg]
  have hnum : 2 * radius ≤ 64 * F * P * seedGridSpacing b P := by
    nlinarith only [hr, Nat.mul_le_mul_left (32 * F) hb]
  have hfloor := Nat.div_mul_le_self (2 * radius) (seedGridSpacing b P)
  nlinarith only [hfloor, hnum, hg]

def localRepresentativeScaleBitBudget (P F B : ℕ) : ℕ :=
  let C := B + 4
  let L := 64 * F * P + 2
  100 * (C + 2) ^ 2 + gridStateBoxBitBudget L C +
    L ^ 2 * (localEligibilityBitBudget C + 3) + L ^ 2 * 4 + B + 6

def localRepresentativesBitBudget (P F B : ℕ) : ℕ :=
  queryExponentsBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (localRepresentativeScaleBitBudget P F B + (64 * F * P + 2) ^ 2 + 3) + 3

theorem localRepresentativesWithWork_cost {n : ℕ} (N P F B : ℕ) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (hPbits : Nat.size P ≤ B) (hP : 0 < P) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hi : ∀ r, (initial r).width ≤ B) :
    (localRepresentativesWithWork N P F a initial query).2 ≤ localRepresentativesBitBudget P F B := by
  let scales := queryExponentsWithWork N F a (initial query)
  let radius := naturalCeilingWithWork (initial query)
  let C := B + 4
  let L := 64 * F * P + 2
  have hscales := queryExponentsWithWork_bounds N F B a (initial query) hB hN hF ha (hi query)
  have hradius : Nat.size (bitWordValue radius.1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length radius.1)).trans
      ((naturalCeilingWithWork_length (initial query)).trans (by have hh := hi query; omega))
  have hradiusCost := (naturalCeilingWithWork_cost (initial query)).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right (hi query) 1) 2))
  let callback := fun e =>
    let b := 2 ^ e
    let spacing := seedGridSpacingWithWork b P
    let points := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue radius.1) query.lo query.hi
    let selected := filterWithWork (fun r => centerEligibilityWithWork b F a (initial r)) points.1
    let labeled := arithmeticMapWithWork (fun r => ((b, r), 1)) selected.1
    (labeled.1, spacing.2 + points.2 + selected.2 + labeled.2 + e + 5)
  have hcallback (e : ℕ) (he : e ∈ scales.1) :
      (callback e).2 ≤ localRepresentativeScaleBitBudget P F B ∧ (callback e).1.length ≤ L ^ 2 := by
    have hmem := he
    change e ∈ (queryExponentsWithWork N F a (initial query)).1 at hmem
    simp only [queryExponentsWithWork, filterWithWork_value] at hmem
    obtain ⟨heRange, heGuard⟩ := List.mem_filter.mp hmem
    have heBound : e ≤ B := by
      have he' := List.mem_range.mp heRange
      rw [Nat.size_eq_bits_len] at he'
      omega
    have hb : Nat.size (2 ^ e) + 2 ≤ C := by rw [Nat.size_pow]; dsimp only [C]; omega
    have hspacing := seedGridSpacingWithWork_bounds (2 ^ e) P C (by omega) (by dsimp only [C]; omega)
    have hgs : 0 < bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1 := by
      rw [seedGridSpacingWithWork_value _ _ hP]
      unfold seedGridSpacing
      omega
    have hgsBits : Nat.size (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1) ≤ C := by
      rw [seedGridSpacingWithWork_value _ _ hP]
      have hdiv : Nat.size ((2 ^ e) / P) ≤ Nat.size (2 ^ e) := Nat.size_le_size (Nat.div_le_self _ _)
      rw [seedGridSpacing]
      rw [Nat.size_pow] at hdiv
      have hmax : max 1 ((2 ^ e) / P) = 1 ∨ max 1 ((2 ^ e) / P) = (2 ^ e) / P := max_choice _ _
      rcases hmax with hh | hh
      · rw [hh, Nat.size_one]
        dsimp only [C]
        omega
      · rw [hh]
        dsimp only [C]
        omega
    have hw := (refinementScaleGuardWithWork_value F (2 ^ e) a (initial query)).mp heGuard
    have hceil : bitWordValue radius.1 ≤ 16 * F * 2 ^ e := by
      rw [naturalCeilingWithWork_value]
      apply Nat.ceil_le.mpr
      have hden : (0 : ℚ) < 16 * F := by
        have hpositive : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
        positivity
      have hh := (div_le_iff₀ hden).mp hw.1
      calc
        _ ≤ ((2 ^ e : ℕ) : ℚ) * (16 * (F : ℚ)) := hh
        _ = ((16 * F * 2 ^ e : ℕ) : ℚ) := by push_cast; ring
    have hcount : 2 * bitWordValue radius.1 /
        bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1 + 2 ≤ L := by
      rw [seedGridSpacingWithWork_value _ _ hP]
      exact query_grid_count P (2 ^ e) _ F hP hceil
    let points := gridStateBoxWithWork n (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
      (bitWordValue radius.1) query.lo query.hi
    have hpCost := (gridStateBoxWithWork_cost n _ _ query.lo query.hi C hgs
      (by dsimp only [C]; omega) hgsBits (by dsimp only [C]; omega)
      ((Nat.size_le_size (query.ordered.trans query.valid)).trans (by dsimp only [C]; omega))
      ((Nat.size_le_size query.valid).trans (by dsimp only [C]; omega))).trans
      (gridStateBoxBitBudget_mono_count _ _ C hcount)
    have hpLen : points.1.length ≤ L ^ 2 := by
      rw [gridStateBoxWithWork_value _ _ _ _ _ hgs]
      exact (localTargetStates_length_le hgs query).trans (Nat.pow_le_pow_left hcount 2)
    have hfilt := filterWithWork_cost
      (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1
      (localEligibilityBitBudget C) (fun r _ => centerEligibilityWithWork_cost (2 ^ e) F C a (initial r)
        (by dsimp only [C]; omega) hb (by dsimp only [C]; omega) (by dsimp only [C]; omega)
        ((hi r).trans (by dsimp only [C]; omega)))
    have hselected : (filterWithWork
        (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1).1.length ≤ L ^ 2 := by
      rw [filterWithWork_value]
      exact (List.length_filter_le _ _).trans hpLen
    have hlabel := arithmeticMapWithWork_cost (fun r : TargetInterval n => ((2 ^ e, r), 1))
      (filterWithWork (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1).1 1
      (fun _ _ => le_rfl)
    have hfilt' := hfilt.trans (Nat.mul_le_mul_right _ hpLen)
    have hlabel' := hlabel.trans (Nat.mul_le_mul_right _ hselected)
    constructor
    · change (seedGridSpacingWithWork (2 ^ e) P).2 + points.2 +
        (filterWithWork (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1).2 +
        (arithmeticMapWithWork (fun r => ((2 ^ e, r), 1))
          (filterWithWork (fun r => centerEligibilityWithWork (2 ^ e) F a (initial r)) points.1).1).2 + e + 5 ≤ _
      have hpc : points.2 ≤ gridStateBoxBitBudget L C := hpCost
      unfold localRepresentativeScaleBitBudget
      change _ ≤ 100 * (C + 2) ^ 2 + gridStateBoxBitBudget L C +
        L ^ 2 * (localEligibilityBitBudget C + 3) + L ^ 2 * 4 + B + 6
      omega
    · simpa only [callback, arithmeticMapWithWork_value, List.length_map] using hselected
  have hflat := arithmeticFlatMapWithWork_cost callback scales.1
    (localRepresentativeScaleBitBudget P F B) (L ^ 2)
    (fun e he => (hcallback e he).1) (fun e he => (hcallback e he).2)
  have hflat' := hflat.trans (Nat.mul_le_mul_right _ hscales.2)
  change scales.2 + radius.2 + (arithmeticFlatMapWithWork callback scales.1).2 + 3 ≤ _
  unfold localRepresentativesBitBudget
  have hsc : scales.2 ≤ queryExponentsBitBudget B := hscales.1
  change radius.2 ≤ _ at hradiusCost
  dsimp only [L] at hflat'
  omega

end BinaryFraction
end EditApproximation

end OAI

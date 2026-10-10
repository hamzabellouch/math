import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGrid
import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialKernel
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal dyadic scales and the finite initial-cone center list, with
binary rational comparisons and bounded grid enumeration. -/

namespace EditApproximation

private theorem log_two_add_one_eq_size (N : ℕ) (hN : 0 < N) :
    Nat.log 2 N + 1 = Nat.size N := by
  apply Nat.le_antisymm
  · have h := Nat.pow_log_le_self 2 hN.ne'
    have hlt : Nat.log 2 N < Nat.size N := Nat.lt_size.mpr h
    omega
  · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N)



@[simp] theorem dyadicScalesWithWork_value (N : ℕ) :
    (dyadicScalesWithWork N).1 = dyadicScales N := by
  have hcount : max 1 N.bits.length = Nat.log 2 N + 1 := by
    by_cases hz : N = 0
    · subst N
      decide
    · have h := log_two_add_one_eq_size N (Nat.pos_of_ne_zero hz)
      have hp := Nat.size_pos.mpr (Nat.pos_of_ne_zero hz)
      rw [Nat.size_eq_bits_len, max_eq_right hp, h]
  simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, powerTwoWord_value, hcount,
    dyadicScales]

theorem dyadicScalesWithWork_cost (N : ℕ) :
    (dyadicScalesWithWork N).2 ≤ (Nat.size N + 1) * (Nat.size N + 9) + 2 := by
  let count := max 1 N.bits.length
  have hc : count ≤ Nat.size N + 1 := by dsimp only [count]; rw [Nat.size_eq_bits_len]; omega
  have hm := arithmeticMapWithWork_cost
    (fun e => (bitWordValue (powerTwoWord e), e + 3)) (List.range count) (count + 3) (by
      intro e he
      have h := List.mem_range.mp he
      omega)
  simp only [List.length_range] at hm
  change (arithmeticMapWithWork _ (List.range count)).2 + N.bits.length + count + 2 ≤ _
  rw [Nat.size_eq_bits_len]
  nlinarith only [hm, hc, Nat.zero_le (Nat.size N)]



@[simp] theorem seedGridSpacingWithWork_value (b P : ℕ) (hP : 0 < P) :
    bitWordValue (seedGridSpacingWithWork b P).1 = seedGridSpacing b P := by
  have hv := (binaryNaturalDivModWithWork_spec b P hP).1
  unfold seedGridSpacingWithWork seedGridSpacing
  dsimp only
  split_ifs with ht
  · have hq : b / P ≤ 1 := by
      have h := (wordLEWithWork_value _ _).mp ht
      change bitWordValue (binaryNaturalDivModWithWork b P).1 ≤ 1 at h
      rwa [hv] at h
    rw [max_eq_left hq]
    rfl
  · have hq : 1 ≤ b / P := by
      have h := mt (wordLEWithWork_value _ _).mpr ht
      change ¬ bitWordValue (binaryNaturalDivModWithWork b P).1 ≤ 1 at h
      rw [hv] at h
      exact Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [max_eq_right hq]
    exact hv

theorem seedGridSpacingWithWork_pos (b P : ℕ) (hP : 0 < P) :
    0 < bitWordValue (seedGridSpacingWithWork b P).1 := by
  rw [seedGridSpacingWithWork_value b P hP]
  unfold seedGridSpacing
  omega

namespace BinaryFraction



@[simp] theorem initialScaleGuardWithWork_value (U b : ℕ) (A : BinaryFraction) :
    (initialScaleGuardWithWork U b A).1 = true ↔
      (U : ℚ) / (16 * A.value ^ 2) ≤ b ∧ (b : ℚ) ≤ 4 * A.value * U := by
  simp only [initialScaleGuardWithWork, Bool.and_eq_true, leWithWork_value,
    canonicalMulWithWork_value, divWithWork_value, nat_value, pow_two]
  norm_num



@[simp] theorem initialCenterGuardWithWork_value (b U : ℕ) (A : BinaryFraction) :
    (initialCenterGuardWithWork b U A).1 = true ↔
      (b : ℚ) / 2 ≤ U ∧ (U : ℚ) ≤ 4 * A.value * b := by
  simp only [initialCenterGuardWithWork, Bool.and_eq_true, leWithWork_value,
    canonicalMulWithWork_value, divWithWork_value, nat_value]
  norm_num

def initialCentersWithWork {n : ℕ} (N P : ℕ) (A : BinaryFraction)
    (U : TargetInterval n → ℕ) (q : TargetInterval n) : List (TargetInterval n) × ℕ :=
  let scales := dyadicScalesWithWork N
  let active := filterWithWork (fun b => initialScaleGuardWithWork (U q) b A) scales.1
  let centers := arithmeticFlatMapWithWork (fun b =>
    let spacing := seedGridSpacingWithWork b P
    let points := gridStateBoxWithWork n (bitWordValue spacing.1) (U q) q.lo q.hi
    let selected := filterWithWork (fun r => initialCenterGuardWithWork b (U r) A) points.1
    (selected.1, spacing.2 + points.2 + selected.2 + 2)) active.1
  (centers.1, scales.2 + active.2 + centers.2 + 3)

@[simp] theorem initialCentersWithWork_value {n : ℕ} (N P : ℕ) (A : BinaryFraction)
    (U : TargetInterval n → ℕ) (q : TargetInterval n) (hP : 0 < P) :
    (initialCentersWithWork N P A U q).1 = localInitialConeCenters N P A.value U q := by
  have hscale (b : ℕ) : (initialScaleGuardWithWork (U q) b A).1 =
      decide ((U q : ℚ) / (16 * A.value ^ 2) ≤ b ∧ (b : ℚ) ≤ 4 * A.value * U q) :=
    Bool.eq_iff_iff.mpr (by simp only [initialScaleGuardWithWork_value, decide_eq_true_eq])
  have hcenter (b : ℕ) (r : TargetInterval n) : (initialCenterGuardWithWork b (U r) A).1 =
      decide ((b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A.value * b) :=
    Bool.eq_iff_iff.mpr (by simp only [initialCenterGuardWithWork_value, decide_eq_true_eq])
  have hgrid (b : ℕ) :
      (gridStateBoxWithWork n (bitWordValue (seedGridSpacingWithWork b P).1)
        (U q) q.lo q.hi).1 = localTargetStates n (seedGridSpacing b P) (U q) q := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (seedGridSpacingWithWork_pos b P hP),
      seedGridSpacingWithWork_value b P hP]
    rfl
  simp only [initialCentersWithWork, arithmeticFlatMapWithWork_value,
    filterWithWork_value, dyadicScalesWithWork_value, hgrid,
    hscale, hcenter, localInitialConeCenters]

def initialProgramWithWork {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (U : TargetInterval n → ℕ) (q : TargetInterval n) : BinaryFraction × ℕ :=
  let centers := initialCentersWithWork N P A U q
  let result := initialMinimumWithWork sourceLength U N F a q centers.1
  (result.1, centers.2 + result.2 + 1)

@[simp] theorem initialProgramWithWork_value {α : Type*} (source target : List α)
    (N P F : ℕ) (A a : BinaryFraction) (U : TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (hP : 0 < P) :
    (initialProgramWithWork source.length N P F A a U q).1.value =
      localInitialConeTable source target U N P F A.value a.value q := by
  simp only [initialProgramWithWork, initialCentersWithWork_value N P A U q hP]
  exact initialMinimumWithWork_value source target U N P F A.value a q

end BinaryFraction
end EditApproximation

end OAI

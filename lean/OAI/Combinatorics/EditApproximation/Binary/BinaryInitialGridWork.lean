import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialGuardWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedListBounds
import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialMinimumWork

namespace OAI

/-! Construction of every local initial-cone center is charged, including
rejected center predicates. The scale test itself bounds the emitted grid. -/

namespace EditApproximation
namespace BinaryFraction

private theorem dyadicScale_size (N B b : ℕ) (hN : Nat.size N ≤ B) (hb : b ∈ dyadicScales N) :
    Nat.size b ≤ B + 2 := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
  have hlen : Nat.log 2 N + 1 = max 1 N.bits.length := by
    simpa only [dyadicScales, List.length_map, List.length_range] using dyadicScales_length_bits N
  have he' := List.mem_range.mp he
  rw [hlen, Nat.size_eq_bits_len] at he'
  rw [Nat.size_pow]
  omega

private theorem initialGrid_count (P b radius Amax : ℕ) (hP : 0 < P)
    (hradius : radius ≤ 16 * Amax ^ 2 * b) :
    2 * radius / seedGridSpacing b P + 2 ≤ 64 * Amax ^ 2 * P + 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hq : b / P ≤ seedGridSpacing b P := le_max_right _ _
  have hdiv := Nat.lt_mul_div_succ b hP
  have hcover : b ≤ 2 * P * seedGridSpacing b P := by nlinarith only [hq, hdiv, hg]
  have hnum : 2 * radius ≤ 64 * Amax ^ 2 * P * seedGridSpacing b P := by
    nlinarith only [hradius, Nat.mul_le_mul_left (32 * Amax ^ 2) hcover]
  have hfloor := Nat.div_mul_le_self (2 * radius) (seedGridSpacing b P)
  nlinarith only [hfloor, hnum, hg]

private theorem initialScale_radius (U b Amax : ℕ) (A : BinaryFraction)
    (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax)
    (hguard : (initialScaleGuardWithWork U b A).1 = true) :
    U ≤ 16 * Amax ^ 2 * b := by
  have hw := (initialScaleGuardWithWork_value U b A).mp hguard
  have hp : 0 < A.value := by linarith
  have hdiv := (div_le_iff₀ (show (0 : ℚ) < 16 * A.value ^ 2 by positivity)).mp hw.1
  have hsq := pow_le_pow_left₀ hp.le hmax 2
  have hmul := mul_le_mul_of_nonneg_right hsq (show (0 : ℚ) ≤ 16 * b by positivity)
  have hh : (U : ℚ) ≤ (16 * Amax ^ 2 * b : ℕ) := by push_cast; nlinarith only [hdiv, hmul]
  exact_mod_cast hh

def initialGridScaleBitBudget (P Amax B : ℕ) : ℕ :=
  let L := 64 * Amax ^ 2 * P + 2
  100 * (B + 6) ^ 2 + gridStateBoxBitBudget L (B + 5) +
    L ^ 2 * (initialCenterGuardBitBudget (B + 4) + 3) + 2

attribute [local irreducible] seedGridSpacingWithWork gridStateBoxWithWork filterWithWork
  initialCenterGuardWithWork initialScaleGuardWithWork

private theorem initialGridScale_bounds {n : ℕ} (N P Amax B b : ℕ)
    (A : BinaryFraction) (U : TargetInterval n → ℕ) (q : TargetInterval n)
    (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hn : Nat.size n ≤ B) (hU : ∀ r, Nat.size (U r) ≤ B) (hAb : A.width ≤ B)
    (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax) (hb : b ∈ dyadicScales N)
    (hguard : (initialScaleGuardWithWork (U q) b A).1 = true) :
    let spacing := seedGridSpacingWithWork b P
    let points := gridStateBoxWithWork n (bitWordValue spacing.1) (U q) q.lo q.hi
    let selected := filterWithWork (fun r => initialCenterGuardWithWork b (U r) A) points.1
    spacing.2 + points.2 + selected.2 + 2 ≤ initialGridScaleBitBudget P Amax B ∧
      selected.1.length ≤ (64 * Amax ^ 2 * P + 2) ^ 2 := by
  dsimp only
  let spacing := seedGridSpacingWithWork b P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) (U q) q.lo q.hi
  let selected := filterWithWork (fun r => initialCenterGuardWithWork b (U r) A) points.1
  let L := 64 * Amax ^ 2 * P + 2
  have hbs := dyadicScale_size N B b hN hb
  have hs := seedGridSpacingWithWork_bounds b P (B + 4) (by omega) (by omega)
  have hsp : Nat.size (bitWordValue spacing.1) ≤ B + 5 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans hs.1
  have hpositive := seedGridSpacingWithWork_pos b P hP
  have hcount := initialGrid_count P b (U q) Amax hP (initialScale_radius (U q) b Amax A hA hmax hguard)
  have hspvalue : bitWordValue spacing.1 = seedGridSpacing b P := seedGridSpacingWithWork_value b P hP
  have hg := gridStateBoxWithWork_cost n (bitWordValue spacing.1) (U q) q.lo q.hi (B + 5)
    hpositive (by omega) hsp (by have := hU q; omega)
    ((Nat.size_le_size (q.ordered.trans q.valid)).trans (by omega))
    ((Nat.size_le_size q.valid).trans (by omega))
  rw [hspvalue] at hg
  have hgc := hg.trans (gridStateBoxBitBudget_mono_count _ L (B + 5) hcount)
  have hpl : points.1.length ≤ L ^ 2 := by
    rw [show points.1 = localTargetStates n (seedGridSpacing b P) (U q) q by
      rw [show points.1 = (gridStateBoxWithWork n (bitWordValue spacing.1) (U q) q.lo q.hi).1 from rfl,
        gridStateBoxWithWork_value _ _ _ _ _ hpositive, hspvalue]
      rfl]
    exact (localTargetStates_length_le (by unfold seedGridSpacing; omega) q).trans
      (Nat.pow_le_pow_left hcount 2)
  have hf := filterWithWork_cost (fun r : TargetInterval n => initialCenterGuardWithWork b (U r) A)
    points.1 (initialCenterGuardBitBudget (B + 4)) (fun r _ =>
      initialCenterGuardWithWork_cost b (U r) (B + 4) A (by omega) (by omega) (by have := hU r; omega) (by omega))
  have hfc := hf.trans (Nat.mul_le_mul_right _ hpl)
  have hselected : selected.1.length ≤ L ^ 2 := by
    exact (show selected.1.length ≤ points.1.length by
      rw [show selected.1 = points.1.filter (fun r => (initialCenterGuardWithWork b (U r) A).1) by
        exact filterWithWork_value _ _]
      exact List.length_filter_le _ _).trans hpl
  refine ⟨?_, hselected⟩
  have hspacing : spacing.2 ≤ 100 * (B + 6) ^ 2 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hs.2
  have hpoints : points.2 ≤ gridStateBoxBitBudget L (B + 5) := by
    dsimp only [points]
    rw [hspvalue]
    exact hgc
  have hfilter : selected.2 ≤ L ^ 2 * (initialCenterGuardBitBudget (B + 4) + 3) := hfc
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hspacing hpoints) hfilter) 2

def initialCentersBitBudget (P Amax B : ℕ) : ℕ :=
  let L := 64 * Amax ^ 2 * P + 2
  (B + 1) * (B + 9) + 2 + (B + 1) * (initialScaleGuardBitBudget (B + 4) + 3) +
    (B + 1) * (initialGridScaleBitBudget P Amax B + L ^ 2 + 3) + 3

theorem initialCentersWithWork_bounds {n : ℕ} (N P Amax B : ℕ)
    (A : BinaryFraction) (U : TargetInterval n → ℕ) (q : TargetInterval n)
    (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hn : Nat.size n ≤ B) (hU : ∀ r, Nat.size (U r) ≤ B) (hAb : A.width ≤ B)
    (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax) :
    (initialCentersWithWork N P A U q).1.length ≤ (B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2 ∧
      (initialCentersWithWork N P A U q).2 ≤ initialCentersBitBudget P Amax B := by
  let scales := dyadicScalesWithWork N
  let active := filterWithWork (fun b => initialScaleGuardWithWork (U q) b A) scales.1
  let callback := fun b =>
    let spacing := seedGridSpacingWithWork b P
    let points := gridStateBoxWithWork n (bitWordValue spacing.1) (U q) q.lo q.hi
    let selected := filterWithWork (fun r => initialCenterGuardWithWork b (U r) A) points.1
    (selected.1, spacing.2 + points.2 + selected.2 + 2)
  let L := 64 * Amax ^ 2 * P + 2
  have hscales : scales.1.length ≤ B + 1 := by
    simp only [scales, dyadicScalesWithWork_value, dyadicScales_length_bits, Nat.size_eq_bits_len]
    omega
  have hactive : active.1.length ≤ B + 1 := by
    exact (show active.1.length ≤ scales.1.length by
      rw [filterWithWork_value]; exact List.length_filter_le _ _).trans hscales
  have hmembers (b : ℕ) (hb : b ∈ active.1) :
      b ∈ dyadicScales N ∧ (initialScaleGuardWithWork (U q) b A).1 = true := by
    have hm := List.mem_filter.mp (show b ∈ scales.1.filter
      (fun b => (initialScaleGuardWithWork (U q) b A).1) by simpa only [active, filterWithWork_value] using hb)
    exact ⟨by simpa only [scales, dyadicScalesWithWork_value] using hm.1, hm.2⟩
  have hcallback (b : ℕ) (hb : b ∈ active.1) :
      (callback b).2 ≤ initialGridScaleBitBudget P Amax B ∧ (callback b).1.length ≤ L ^ 2 :=
    initialGridScale_bounds N P Amax B b A U q hB hP hN hPb hn hU hAb hA hmax
      (hmembers b hb).1 (hmembers b hb).2
  have hg := filterWithWork_cost (fun b => initialScaleGuardWithWork (U q) b A)
    scales.1 (initialScaleGuardBitBudget (B + 4)) (by
      intro b hb
      have hmem : b ∈ dyadicScales N := by simpa only [scales, dyadicScalesWithWork_value] using hb
      have hbb := dyadicScale_size N B b hN hmem
      exact initialScaleGuardWithWork_cost (U q) b (B + 4) A (by omega)
        (by have := hU q; omega) (by omega) (by omega))
  have hgc := hg.trans (Nat.mul_le_mul_right _ hscales)
  have hc := arithmeticFlatMapWithWork_cost callback active.1 (initialGridScaleBitBudget P Amax B)
    (L ^ 2) (fun b hb => (hcallback b hb).1) (fun b hb => (hcallback b hb).2)
  have hcc := hc.trans (Nat.mul_le_mul_right _ hactive)
  have hs := dyadicScalesWithWork_cost N
  have hsc : scales.2 ≤ (B + 1) * (B + 9) + 2 := by
    exact hs.trans (Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 2)
  constructor
  · rw [show (initialCentersWithWork N P A U q).1 = active.1.flatMap (fun b => (callback b).1) by
      exact arithmeticFlatMapWithWork_value callback active.1]
    exact (list_flatMap_length_le _ _ _ (fun b hb => (hcallback b hb).2)).trans
      (Nat.mul_le_mul_right _ hactive)
  · change scales.2 + active.2 + (arithmeticFlatMapWithWork callback active.1).2 + 3 ≤ _
    change active.2 ≤ _ at hgc
    unfold initialCentersBitBudget
    dsimp only
    simp only [L] at hcc ⊢
    omega

def initialProgramBitBudget (P Amax B : ℕ) : ℕ :=
  initialCentersBitBudget P Amax B +
    initialMinimumBitBudget ((B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2) (B + 4) + 1

private theorem initialMinimumBitBudget_mono_count (n m B : ℕ) (h : n ≤ m) :
    initialMinimumBitBudget n B ≤ initialMinimumBitBudget m B := by
  unfold initialMinimumBitBudget
  gcongr

theorem initialProgramWithWork_bounds {n : ℕ} (sourceLength N P F Amax B : ℕ)
    (A a : BinaryFraction) (U : TargetInterval n → ℕ) (q : TargetInterval n)
    (hB : 8 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F ≤ B) (hs : Nat.size sourceLength ≤ B) (hn : Nat.size n ≤ B)
    (hU : ∀ r, Nat.size (U r) ≤ B) (hAb : A.width ≤ B) (ha : a.width ≤ B)
    (hA : 1 ≤ A.value) (hmax : A.value ≤ Amax) :
    (initialProgramWithWork sourceLength N P F A a U q).1.width ≤ initialMinimumWordBudget (B + 4) ∧
      (initialProgramWithWork sourceLength N P F A a U q).2 ≤ initialProgramBitBudget P Amax B := by
  let centers := initialCentersWithWork N P A U q
  have hc := initialCentersWithWork_bounds N P Amax B A U q hB hP hN hPb hn hU hAb hA hmax
  have hm := initialMinimumWithWork_bounds sourceLength U N F a q centers.1 (B + 4)
    (by omega) (by omega) (by have := hU q; omega) (by omega) (by omega) (by omega)
    ((Nat.add_le_add_right (Nat.size_le_size (q.ordered.trans q.valid)) 2).trans (by omega))
    ((Nat.add_le_add_right (Nat.size_le_size q.valid) 2).trans (by omega)) (by
      intro r _
      exact ⟨by have := hU r; omega,
        (Nat.add_le_add_right (Nat.size_le_size (r.ordered.trans r.valid)) 2).trans (by omega),
        (Nat.add_le_add_right (Nat.size_le_size r.valid) 2).trans (by omega)⟩)
  have hmc := hm.2.trans (initialMinimumBitBudget_mono_count _ _ (B + 4) hc.1)
  refine ⟨hm.1, ?_⟩
  change centers.2 + (initialMinimumWithWork sourceLength U N F a q centers.1).2 + 1 ≤ _
  unfold initialProgramBitBudget
  have hcc : centers.2 ≤ initialCentersBitBudget P Amax B := hc.2
  omega

end BinaryFraction
end EditApproximation

end OAI

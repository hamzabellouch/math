import OAI.Combinatorics.EditApproximation.Refinement.ComputedSeed
import OAI.Combinatorics.EditApproximation.Geometry.DomainCounts
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Simultaneous seed failure with the computed parameters

The count includes every dyadic guess, complete coarse-tree node and shift.
Independent finite entry streams realize the actual full table law.
Symbolic recursion indices carry exact equalities to the computed parameters.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem twice_square_le_two_pow (r : ℕ) (hr : 8 ≤ r) : 2 * r ^ 2 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [pow_succ 2 r]
    nlinarith

theorem computed_coarse_B_upper (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    (integerParameters N).B ≤ 2 ^ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  have hp : coarseExponent (inputSmallLog N) ≤ 2 * heightExponent N := by
    have hsqrt := (Nat.sqrt_le_self (Nat.sqrt (Nat.log 2 (inputSmallLog N)))).trans
      (Nat.sqrt_le_self (Nat.log 2 (inputSmallLog N)))
    exact hsqrt.trans ((Nat.log_le_self _ _).trans (by omega))
  have hpoly := twice_square_le_two_pow (heightExponent N) hr
  have hexponent : heightExponent N * coarseExponent (inputSmallLog N) ≤ inputHeight N := by
    have hmul := Nat.mul_le_mul_left (heightExponent N) hp
    change _ ≤ 2 ^ heightExponent N
    nlinarith
  change (2 ^ heightExponent N) ^ coarseExponent (inputSmallLog N) ≤ 2 ^ inputHeight N
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hexponent

theorem computed_coarse_height_large (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    256 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  change 2 ^ 8 ≤ 2 ^ heightExponent N
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hr

theorem coarseInternalNodes_add_one_le_pow (B D : ℕ) (hB : 2 ≤ B) :
    coarseInternalNodes B D + 1 ≤ B ^ D := by
  induction D with
  | zero => simp only [coarseInternalNodes, zero_add, pow_zero, le_refl]
  | succ D ih =>
    have hmul := Nat.mul_le_mul_left B ih
    simp only [coarseInternalNodes, pow_succ]
    nlinarith

/-- Multiplicity of all local Bernstein tails for one complete entry. -/
def coarseEntryTailCount (B D n : ℕ) : ℕ :=
  (Nat.clog 2 n + 1) * coarseInternalNodes B D * (4 * (2 * 2 ^ Nat.clog 2 n + 1))

theorem computed_coarseEntryTailCount (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    coarseEntryTailCount (integerParameters N).B (computedCoarseDepth N n) n ≤
      2 ^ (4 * inputHeight N + 4) := by
  let H := inputHeight N
  let B := (integerParameters N).B
  have hBtwo : 2 ≤ B := by
    have hbranch := computed_coarse_branching N hN hell
    dsimp [B]
    omega
  have hBupper : B ≤ 2 ^ H := computed_coarse_B_upper N hN hell
  have hnmax : max 1 n ≤ 2 ^ H := by
    apply max_le Nat.one_le_two_pow
    exact hn.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hnupper : n ≤ 2 ^ H := (le_max_right 1 n).trans hnmax
  have hlog : Nat.clog 2 n ≤ H := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hnupper
  have hguesses : Nat.clog 2 n + 1 ≤ 2 ^ H := by
    have hself := Nat.lt_pow_self (by decide : 1 < 2) (n := H)
    omega
  have hnodes : coarseInternalNodes B (computedCoarseDepth N n) ≤ 2 ^ (2 * H) := by
    have hcount := coarseInternalNodes_add_one_le_pow B (computedCoarseDepth N n) hBtwo
    have hpower := intervalTreeDepth_power_le B n hBtwo
    have hproduct : B * max 1 n ≤ 2 ^ H * 2 ^ H := Nat.mul_le_mul hBupper hnmax
    rw [← pow_add] at hproduct
    change B ^ computedCoarseDepth N n ≤ B * max 1 n at hpower
    have hsum : H + H = 2 * H := by omega
    rw [hsum] at hproduct
    omega
  have hguessPower : 2 ^ Nat.clog 2 n ≤ 2 ^ H := Nat.pow_le_pow_right (by decide : 0 < 2) hlog
  have hshift : 4 * (2 * 2 ^ Nat.clog 2 n + 1) ≤ 2 ^ (H + 4) := by
    have hone := Nat.one_le_two_pow (n := H)
    rw [pow_add]
    norm_num only [show (2 : ℕ) ^ 4 = 16 by norm_num]
    nlinarith
  have hproduct := Nat.mul_le_mul (Nat.mul_le_mul hguesses hnodes) hshift
  apply hproduct.trans_eq
  rw [← pow_add, ← pow_add]
  congr 1
  omega

theorem computed_coarse_tail_exponent (N : ℕ) :
    -(initialLambda N : ℝ) * initialThresholdQ N / 12 = -(inputHeight N : ℝ) ^ 3 / 768 := by
  have hH : (inputHeight N : ℝ) ≠ 0 := by
    have hpos : 0 < inputHeight N := by unfold inputHeight; positivity
    exact_mod_cast hpos.ne'
  simp only [initialLambda, initialThresholdQ, Rat.cast_div, Rat.cast_mul,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow]
  field_simp [hH]
  ring

theorem coarse_global_exponential_failure (H : ℕ) (hH : 256 ≤ H) :
    (2 : ℝ) ^ (10 * H) * Real.exp (-(H : ℝ) ^ 3 / 768) < 1 / 100 := by
  have hHr : (256 : ℝ) ≤ H := by exact_mod_cast hH
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (10 * H)
  rw [← Real.exp_nat_mul, mul_one] at hpower
  have hexponent : (10 * H : ℕ) - (H : ℝ) ^ 3 / 768 ≤ -7 := by
    have hsq : (65536 : ℝ) ≤ (H : ℝ) ^ 2 := by nlinarith
    have hcube := mul_le_mul_of_nonneg_right hsq (show (0 : ℝ) ≤ H by positivity)
    push_cast
    nlinarith
  have hseven : (128 : ℝ) ≤ Real.exp 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one,
      show (2 : ℝ) ^ 7 = 128 by norm_num] using h
  have hnegative : Real.exp (-7) ≤ (1 : ℝ) / 128 := by
    rw [Real.exp_neg, ← one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hseven
  calc
    _ ≤ Real.exp (10 * H : ℕ) * Real.exp (-(H : ℝ) ^ 3 / 768) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_nonneg _)
    _ = Real.exp ((10 * H : ℕ) - (H : ℝ) ^ 3 / 768) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-7) := Real.exp_le_exp.mpr hexponent
    _ ≤ 1 / 128 := hnegative
    _ < 1 / 100 := by norm_num

/-- Symbolic recursion indices prevent irrelevant normalization of integer
logarithms in dependent draw types. The equalities retain the exact computed
algorithm, rather than replacing it with a larger or assumed seed contract. -/
theorem computed_initialAccuracy_failure (N B D : ℕ)
    [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (hB : B = (integerParameters N).B)
    {α : Type*} [DecidableEq α] (x y : List α)
    (hD : D = computedCoarseDepth N (coarseEntryWidth x y))
    (hN : 0 < N) (hwidth : coarseEntryWidth x y ≤ N)
    (hell : 200 ≤ inputSmallLog N)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseInitialMeasure B D (coarseEntryWidth x y)).real
      {draws | ¬ CoarseInitialAccuracyEvent B D (initialThresholdQ N) (initialLambda N) x y draws} ≤
      (2 : ℝ) ^ (4 * inputHeight N + 4) * Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) := by
  have hH : (256 : ℚ) ≤ inputHeight N := by exact_mod_cast computed_coarse_height_large N hN hell
  have hQ : (2 : ℚ) ≤ initialThresholdQ N := by
    unfold initialThresholdQ
    exact (by norm_num : (2 : ℚ) ≤ 256 ^ 4).trans
      (pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 256) hH 4)
  have hden : (0 : ℚ) < 64 * inputHeight N :=
    mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 256) hH)
  have hlam : (0 : ℚ) < initialLambda N := by
    unfold initialLambda
    exact div_pos (by norm_num) hden
  have hlamone : initialLambda N < 1 := by
    unfold initialLambda
    apply (div_lt_one hden).2
    linarith only [hH]
  have hfailure := coarseInitialAccuracyEvent_failure (B := B) (D := D)
    (initialThresholdQ N) (initialLambda N) x y hQ hlam hlamone bernstein
  rw [computed_coarse_tail_exponent] at hfailure
  have hcount : coarseEntryTailCount B D (coarseEntryWidth x y) ≤
      2 ^ (4 * inputHeight N + 4) := by
    rw [hB, hD]
    exact computed_coarseEntryTailCount N (coarseEntryWidth x y) hN hwidth hell
  have hcountReal : (coarseEntryTailCount B D (coarseEntryWidth x y) : ℝ) ≤
      (2 : ℝ) ^ (4 * inputHeight N + 4) := by exact_mod_cast hcount
  have hfailureCount : (coarseInitialMeasure B D (coarseEntryWidth x y)).real
      {draws | ¬ CoarseInitialAccuracyEvent B D
        (initialThresholdQ N) (initialLambda N) x y draws} ≤
      (coarseEntryTailCount B D (coarseEntryWidth x y) : ℝ) *
        Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) := by
    convert hfailure using 1
    simp only [coarseEntryTailCount, Nat.cast_mul, Nat.cast_ofNat]
    ring
  exact hfailureCount.trans (mul_le_mul_of_nonneg_right hcountReal (Real.exp_nonneg _))





instance coarseFullSeedMeasure_isProbabilityMeasure (B : ℕ) [NeZero B]
    {I α : Type*} [Fintype I] (depth : I → ℕ) (x y : I → List α)
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    IsProbabilityMeasure (coarseFullSeedMeasure B depth x y) := by
  unfold coarseFullSeedMeasure
  infer_instance

noncomputable def CoarseFullSeedAccuracyEvent (N B : ℕ) {I α : Type*} [DecidableEq α]
    (depth : I → ℕ) (x y : I → List α) (draws : CoarseFullSeedDraws B depth x y) : Prop :=
  ∀ i, CoarseInitialAccuracyEvent B (depth i)
    (initialThresholdQ N) (initialLambda N) (x i) (y i) (draws i)

/-- The full finite table law fails with probability below one percent.
The cardinal bound is supplied by the actual labeled state-domain count. -/
theorem computed_fullSeed_failure (N B : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    {I α : Type*} [Fintype I] [DecidableEq α] (depth : I → ℕ)
    (x y : I → List α) (hB : B = (integerParameters N).B)
    (hD : ∀ i, depth i = computedCoarseDepth N (coarseEntryWidth (x i) (y i)))
    (hN : 0 < N) (hwidth : ∀ i, coarseEntryWidth (x i) (y i) ≤ N)
    (hcount : Fintype.card I ≤ 2 ^ (5 * inputHeight N))
    (hell : 200 ≤ inputSmallLog N)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseFullSeedMeasure B depth x y).real
      {draws | ¬ CoarseFullSeedAccuracyEvent N B depth x y draws} < 1 / 100 := by
  classical
  let μ := coarseFullSeedMeasure B depth x y
  let ν (i : I) := coarseInitialMeasure B (depth i) (coarseEntryWidth (x i) (y i))
  let bad (i : I) : Set (CoarseGuessIndex (coarseEntryWidth (x i) (y i)) →
      CoarseThresholdDraws B (depth i)) :=
    {draws | ¬ CoarseInitialAccuracyEvent B (depth i)
      (initialThresholdQ N) (initialLambda N) (x i) (y i) draws}
  have hsubset : {draws | ¬ CoarseFullSeedAccuracyEvent N B depth x y draws} ⊆
      ⋃ i, {draws | draws i ∈ bad i} := by
    intro draws hdraws
    obtain ⟨i, hi⟩ := not_forall.mp hdraws
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hprojection (i : I) : μ.real {draws | draws i ∈ bad i} = (ν i).real (bad i) := by
    have hmap := (measurePreserving_eval (μ := ν) i).map_eq
    have hpreimage := Measure.map_apply (μ := Measure.pi ν) (measurable_pi_apply i)
      (Set.toFinite (bad i)).measurableSet
    rw [hmap] at hpreimage
    exact congrArg ENNReal.toReal hpreimage.symm
  have hpoint (i : I) : μ.real {draws | draws i ∈ bad i} ≤
      (2 : ℝ) ^ (4 * inputHeight N + 4) * Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) := by
    rw [hprojection]
    exact computed_initialAccuracy_failure N B (depth i) hB (x i) (y i) (hD i)
      hN (hwidth i) hell bernstein
  have hH : 256 ≤ inputHeight N := computed_coarse_height_large N hN hell
  have htotal : Fintype.card I * 2 ^ (4 * inputHeight N + 4) ≤ 2 ^ (10 * inputHeight N) := by
    calc
      _ ≤ 2 ^ (5 * inputHeight N) * 2 ^ (4 * inputHeight N + 4) := Nat.mul_le_mul_right _ hcount
      _ = 2 ^ (9 * inputHeight N + 4) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have htotalReal : (Fintype.card I : ℝ) * (2 : ℝ) ^ (4 * inputHeight N + 4) ≤
      (2 : ℝ) ^ (10 * inputHeight N) := by exact_mod_cast htotal
  calc
    _ ≤ μ.real (⋃ i, {draws | draws i ∈ bad i}) := measureReal_mono hsubset
    _ ≤ ∑ i, μ.real {draws | draws i ∈ bad i} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : I, (2 : ℝ) ^ (4 * inputHeight N + 4) * Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) :=
      sum_le_sum (fun i _ => hpoint i)
    _ = ((Fintype.card I : ℝ) * (2 : ℝ) ^ (4 * inputHeight N + 4)) *
        Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) := by simp only [sum_const, card_univ, nsmul_eq_mul, mul_assoc]
    _ ≤ (2 : ℝ) ^ (10 * inputHeight N) * Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) :=
      mul_le_mul_of_nonneg_right htotalReal (Real.exp_nonneg _)
    _ < 1 / 100 := coarse_global_exponential_failure _ hH

/-- The executable full integer table uses exactly the supplied recursion
indices. Computed-parameter equalities appear only in its correctness proofs. -/


theorem computed_fullSeedTable_pathwise (N B : ℕ) {I α : Type*} [DecidableEq α]
    (depth : I → ℕ) (x y : I → List α) (hB : B = (integerParameters N).B)
    (hD : ∀ i, depth i = computedCoarseDepth N (coarseEntryWidth (x i) (y i)))
    (hN : 0 < N) (hwidth : ∀ i, coarseEntryWidth (x i) (y i) ≤ N)
    (hell : 200 ≤ inputSmallLog N) (draws : CoarseFullSeedDraws B depth x y)
    (hevent : CoarseFullSeedAccuracyEvent N B depth x y draws) :
    ∀ i, EditDistortion.edit (x i) (y i) ≤ coarseFullSeedTable N B depth x y draws i ∧
      coarseFullSeedTable N B depth x y draws i ≤
        (integerParameters N).initialFactor * EditDistortion.edit (x i) (y i) := by
  intro i
  exact computed_initialSeed_bounds N B (depth i) (x i) (y i) hB (hD i)
    hN (hwidth i) hell (draws i) (hevent i)

/-- Every actual table value is clamped, and all zero-cost entries remain
zero even on executions outside the simultaneous accuracy event. -/
theorem computed_fullSeedTable_range_zero (N B : ℕ) {I α : Type*} [DecidableEq α]
    (depth : I → ℕ) (x y : I → List α) (draws : CoarseFullSeedDraws B depth x y) :
    ∀ i, coarseFullSeedTable N B depth x y draws i ≤ N ∧
      (EditDistortion.edit (x i) (y i) = 0 → coarseFullSeedTable N B depth x y draws i = 0) := by
  intro i
  exact ⟨coarseInitialValue_le_length _ _ _ _ _ _ _ _,
    coarseInitialValue_zero _ _ _ _ _ _ _ _⟩

/-- Simultaneous finite table accuracy under the scalar Bernstein hypothesis. -/
theorem computed_fullSeedTable_accuracy (N B : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    {I α : Type*} [Fintype I] [DecidableEq α] (depth : I → ℕ) (x y : I → List α)
    (hB : B = (integerParameters N).B)
    (hD : ∀ i, depth i = computedCoarseDepth N (coarseEntryWidth (x i) (y i)))
    (hN : 0 < N) (hwidth : ∀ i, coarseEntryWidth (x i) (y i) ≤ N)
    (hcount : Fintype.card I ≤ 2 ^ (5 * inputHeight N))
    (hell : 200 ≤ inputSmallLog N)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseFullSeedMeasure B depth x y).real {draws | ¬ ∀ i,
      EditDistortion.edit (x i) (y i) ≤ coarseFullSeedTable N B depth x y draws i ∧
      coarseFullSeedTable N B depth x y draws i ≤
        (integerParameters N).initialFactor * EditDistortion.edit (x i) (y i)} < 1 / 100 := by
  have hsubset : {draws | ¬ ∀ i,
      EditDistortion.edit (x i) (y i) ≤ coarseFullSeedTable N B depth x y draws i ∧
      coarseFullSeedTable N B depth x y draws i ≤
        (integerParameters N).initialFactor * EditDistortion.edit (x i) (y i)} ⊆
      {draws | ¬ CoarseFullSeedAccuracyEvent N B depth x y draws} := by
    intro draws hdraws hevent
    exact hdraws (computed_fullSeedTable_pathwise N B depth x y hB hD hN hwidth hell draws hevent)
  exact (measureReal_mono hsubset).trans_lt
    (computed_fullSeed_failure N B depth x y hB hD hN hwidth hcount hell bernstein)

end EditApproximation

end OAI

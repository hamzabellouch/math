import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealCells
import OAI.NumberTheory.Ostmann.Arithmetic.MovingIntegerCells
import OAI.NumberTheory.Ostmann.Arithmetic.CommonRootMesh

namespace OAI

/-! # Canonical residue coefficients of the original moving weight -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingResidueCoefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (a b : ℕ) : ℂ :=
  (movingResidueFlag nodes (topGiantInput a b) * movingSpectatorResidue q value g D S T a b) *
    movingDataWeight F E T

theorem movingResidueCoefficient_norm {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (a b : ℕ) :
    ‖movingResidueCoefficient q value F E g D S T nodes a b‖ ≤
      ‖movingDataWeight F E T‖ * ∏ i ∈ S, B i ^ (2 ^ n) := by
  have hb := movingSpectatorResidue_norm q value g D S B hB hg T a b
  unfold movingResidueCoefficient movingResidueFlag
  split_ifs
  · rw [one_mul, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  · simp only [zero_mul, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i hi => pow_nonneg (hB i hi) _)

theorem moving_original_canonical_coefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingArithmeticIndicator value childBound pivotBound T XL XR *
        movingWindowedSpectatorWeight q value F E X lo hi g D S T XL XR =
      movingResidueCoefficient q value F E g D S T nodes a b *
        movingRealGateWeight value T nodes X lo hi (topGiantReal XL XR) := by
  dsimp only
  rw [moving_original_nonsmooth_residue_factor q value hvalue childBound pivotBound F E
    X lo hi g D S T hf XL XR a b M hM hMq hL hR]
  simp only [movingResidueCoefficient, movingRealGateWeight, topGiantReal, Bool.false_eq_true,
    ite_false, ite_true]
  ring

theorem moving_canonical_prime_interval {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) (u v : ℝ) (f : ℝ → ℂ) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    complexPrimeInterval M a u v (fun y =>
      (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
        movingWindowedSpectatorWeight q value F E X lo hi g D S T ⌊Real.exp y⌋₊ XR) * f y) =
    complexPrimeInterval M a u v (fun y =>
      (movingResidueCoefficient q value F E g D S T nodes a b *
        movingRealGateWeight value T nodes X lo hi (topGiantReal (Real.exp y) XR)) * f y) := by
  dsimp only
  apply complexPrimeInterval_congr
  intro p hp hprime hpa
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  rw [Real.exp_log hp0, Nat.floor_natCast,
    moving_original_canonical_coefficient q value hvalue childBound pivotBound F E X lo hi
      g D S T hf p XR a b M hM hMq (Int.natCast_modEq_iff.mpr hpa) hR]

theorem moving_canonical_integer_interval {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) (u v G : ℝ) (f : ℝ → ℂ) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    complexIntegerInterval M a u v G (fun y =>
      (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
        movingWindowedSpectatorWeight q value F E X lo hi g D S T ⌊Real.exp y⌋₊ XR) * f y) =
    complexIntegerInterval M a u v G (fun y =>
      (movingResidueCoefficient q value F E g D S T nodes a b *
        movingRealGateWeight value T nodes X lo hi (topGiantReal (Real.exp y) XR)) * f y) := by
  dsimp only
  apply complexIntegerInterval_congr
  intro p hp hpa
  have hp0 : (0 : ℝ) < p := by
    have : 0 < p := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hp).1
    exact_mod_cast this
  rw [Real.exp_log hp0, Nat.floor_natCast,
    moving_original_canonical_coefficient q value hvalue childBound pivotBound F E X lo hi
      g D S T hf p XR a b M hM hMq (Int.natCast_modEq_iff.mpr hpa) hR]

end Ostmann

end OAI

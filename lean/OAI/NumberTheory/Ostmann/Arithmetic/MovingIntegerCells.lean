import OAI.NumberTheory.Ostmann.Arithmetic.RootCellIntegerComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCells

namespace OAI

/-! # The literal moving arithmetic and spectator weights for integer giants -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem complexIntegerInterval_congr (q a : ℕ) (u v G : ℝ) (w g : ℝ → ℂ)
    (h : ∀ n ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      Nat.ModEq q n a → w (Real.log n) = g (Real.log n)) :
    complexIntegerInterval q a u v G w = complexIntegerInterval q a u v G g := by
  unfold complexIntegerInterval
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : Nat.ModEq q n a
  · rw [h n hn hc]
  · simp only [integerResidueAtom, ite_eq_right hc, Complex.ofReal_zero, mul_zero]

theorem movingSupportedIntegerInterval_cells {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M : ℕ)
    (S : Finset ℝ) (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hS : movingTopRootCuts value hvalue childBound pivotBound T hf XR ⊆ S)
    (w : ℕ → ℂ)
    (hw : ∀ XL YL, T.ArithmeticSupport value childBound pivotBound XL XR →
      T.ArithmeticSupport value childBound pivotBound YL XR →
      (XL : ℤ) ≡ (YL : ℤ) [ZMOD M] →
      rootCellCode S (XL : ℝ) = rootCellCode S (YL : ℝ) → w XL = w YL)
    (u v G : ℝ) (f : ℝ → ℂ) :
    complexIntegerInterval M a u v G (fun y =>
      (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
        w ⌊Real.exp y⌋₊) * f y) =
    complexIntegerInterval M a u v G (fun y =>
      movingSupportedCellValue value childBound pivotBound T XR a M S w
        (rootCellCode S (Real.exp y)) * f y) := by
  apply complexIntegerInterval_congr
  intro p hp hpa
  have hp0 : (0 : ℝ) < p := by
    have : 0 < p := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hp).1
    exact_mod_cast this
  rw [Real.exp_log hp0, Nat.floor_natCast]
  rw [movingSupportedCellValue_eq value hvalue childBound pivotBound T hf XR a M S hM hS
    w hw p (Int.natCast_modEq_iff.mpr hpa)]

theorem moving_supported_integer_comparison {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hM0 : 0 < M) (u v G : ℝ) (huv : u ≤ v)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) (S : Finset ℝ)
    (hS : movingTopRootCuts value hvalue childBound pivotBound T hf XR ⊆ S)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hwB : ∀ XL, T.ArithmeticSupport value childBound pivotBound XL XR → ‖w XL‖ ≤ B)
    (hw : ∀ XL YL, T.ArithmeticSupport value childBound pivotBound XL XR →
      T.ArithmeticSupport value childBound pivotBound YL XR →
      (XL : ℤ) ≡ (YL : ℤ) [ZMOD M] →
      rootCellCode S (XL : ℝ) = rootCellCode S (YL : ℝ) → w XL = w YL) :
    ∃ (s : ℕ → ℝ) (N : ℕ) (d : ℕ → ℂ),
      Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧ (∀ j, ‖d j‖ ≤ B) ∧
      ‖complexIntegerInterval M a u v G (fun y =>
          (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
            w ⌊Real.exp y⌋₊) * smoothPolynomialWeight F (Real.exp y)) -
        ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
          d j * smoothPolynomialWeight F (Real.exp y) * (integerLogDensity M G y : ℂ)‖ ≤
        4 * ((S.card + 1 : ℕ) : ℝ) * B * smoothPolynomialBudget F * Real.exp (-G) := by
  obtain ⟨s, N, d, hs, hs0, hsN, hN, hd, herr⟩ := root_cell_integer_comparison hM0 u v G huv F S hroots
    (movingSupportedCellValue value childBound pivotBound T XR a M S w) B hB
    (movingSupportedCellValue_norm value childBound pivotBound T XR a M S w B hB hwB)
  refine ⟨s, N, d, hs, hs0, hsN, hN, hd, ?_⟩
  rw [movingSupportedIntegerInterval_cells value hvalue childBound pivotBound T hf XR a M S hM hS w hw]
  exact herr

theorem moving_spectator_integer_comparison {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hM0 : 0 < M) (u v G : ℝ) (huv : u ≤ v) {k : ℕ} (F : Fin k → ClippedPolynomialFactor) :
    ∃ (s : ℕ → ℝ) (N : ℕ) (d : ℕ → ℂ),
      Monotone s ∧ s 0 = u ∧ s N = v ∧
      N ≤ (movingTopRootCuts value hvalue childBound pivotBound T hf XR).card +
        (∑ i, (F i).polynomial.derivative.natDegree) + 1 ∧
      (∀ j, ‖d j‖ ≤ ∏ i ∈ S, B i ^ (2 ^ n)) ∧
      ‖complexIntegerInterval M a u v G (fun y =>
          (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
            ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T ⌊Real.exp y⌋₊ XR) *
              smoothPolynomialWeight F (Real.exp y)) -
        ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
          d j * smoothPolynomialWeight F (Real.exp y) * (integerLogDensity M G y : ℂ)‖ ≤
        4 * (((movingTopRootCuts value hvalue childBound pivotBound T hf XR).card +
          (∑ i, (F i).polynomial.derivative.natDegree) + 1 : ℕ) : ℝ) *
          (∏ i ∈ S, B i ^ (2 ^ n)) * smoothPolynomialBudget F * Real.exp (-G) := by
  let roots := movingPrimeRootCuts value hvalue childBound pivotBound T hf XR F
  let w := fun XL => ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR
  have hS : movingTopRootCuts value hvalue childBound pivotBound T hf XR ⊆ roots :=
    Finset.subset_union_left
  have hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ roots := by
    intro i r hr
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩)
  have hprod : 0 ≤ ∏ i ∈ S, B i ^ (2 ^ n) := by
    apply Finset.prod_nonneg
    intro i hi
    exact pow_nonneg (hB i hi) _
  have hw : ∀ XL YL, T.ArithmeticSupport value childBound pivotBound XL XR →
      T.ArithmeticSupport value childBound pivotBound YL XR →
      (XL : ℤ) ≡ (YL : ℤ) [ZMOD M] →
      rootCellCode roots (XL : ℝ) = rootCellCode roots (YL : ℝ) → w XL = w YL := by
    intro XL YL hX hY hres _
    exact movingSpectatorProduct_modEq q value hvalue g D S T hf M XL XR YL hMq
      (hX.integral value hvalue childBound pivotBound T XL XR)
      (hY.integral value hvalue childBound pivotBound T YL XR) hres
  obtain ⟨s, N, d, hs, hs0, hsN, hN, hd, herr⟩ := root_cell_integer_comparison hM0 u v G huv F
    roots hroots (movingSupportedCellValue value childBound pivotBound T XR a M roots w)
    (∏ i ∈ S, B i ^ (2 ^ n)) hprod
    (movingSupportedCellValue_norm value childBound pivotBound T XR a M roots w _ hprod
      (fun XL _ => movingSpectatorProduct_norm q value g D S B hB hg T XL XR))
  have hcard := Nat.add_le_add_right (movingPrimeRootCuts_card value hvalue childBound pivotBound T hf XR F) 1
  refine ⟨s, N, d, hs, hs0, hsN, hN.trans hcard, hd, ?_⟩
  rw [movingSupportedIntegerInterval_cells value hvalue childBound pivotBound T hf XR a M roots hM hS w hw]
  apply herr.trans
  gcongr
  exact smoothPolynomialBudget_nonneg F

end Ostmann

end OAI

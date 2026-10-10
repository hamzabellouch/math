import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticCells

namespace OAI

/-! # Cell values for supported residue weights -/

namespace Ostmann
open scoped Classical BigOperators
open MeasureTheory

noncomputable def movingSupportedCellValue {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (XR a M : ℕ) (S : Finset ℝ) (w : ℕ → ℂ) (code : S → Ordering) : ℂ :=
  if h : ∃ XL : ℕ, (XL : ℤ) ≡ (a : ℤ) [ZMOD M] ∧
      rootCellCode S (XL : ℝ) = code ∧ T.ArithmeticSupport value childBound pivotBound XL XR
  then w (Classical.choose h) else 0

theorem movingSupportedCellValue_norm {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (XR a M : ℕ) (S : Finset ℝ) (w : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ XL, T.ArithmeticSupport value childBound pivotBound XL XR → ‖w XL‖ ≤ B)
    (code : S → Ordering) :
    ‖movingSupportedCellValue value childBound pivotBound T XR a M S w code‖ ≤ B := by
  unfold movingSupportedCellValue
  split_ifs with h
  · exact hw _ (Classical.choose_spec h).2.2
  · simpa only [norm_zero] using hB

/-- The cell representative is used only on the proved original support.
Its value is independent of the representative by the supplied local identity. -/
theorem movingSupportedCellValue_eq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M : ℕ)
    (S : Finset ℝ) (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hS : movingTopRootCuts value hvalue childBound pivotBound T hf XR ⊆ S)
    (w : ℕ → ℂ)
    (hw : ∀ XL YL, T.ArithmeticSupport value childBound pivotBound XL XR →
      T.ArithmeticSupport value childBound pivotBound YL XR →
      (XL : ℤ) ≡ (YL : ℤ) [ZMOD M] →
      rootCellCode S (XL : ℝ) = rootCellCode S (YL : ℝ) → w XL = w YL)
    (XL : ℕ) (hres : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) :
    movingArithmeticIndicator value childBound pivotBound T XL XR * w XL =
      movingSupportedCellValue value childBound pivotBound T XR a M S w
        (rootCellCode S (XL : ℝ)) := by
  unfold movingSupportedCellValue movingArithmeticIndicator
  by_cases hX : T.ArithmeticSupport value childBound pivotBound XL XR
  · have hE : ∃ YL : ℕ, (YL : ℤ) ≡ (a : ℤ) [ZMOD M] ∧
        rootCellCode S (YL : ℝ) = rootCellCode S (XL : ℝ) ∧
        T.ArithmeticSupport value childBound pivotBound YL XR := ⟨XL, hres, rfl, hX⟩
    rw [ite_eq_left hX, dite_eq_left hE, one_mul]
    have hc := Classical.choose_spec hE
    exact hw XL _ hX hc.2.2 (hres.trans hc.1.symm) hc.2.1.symm
  · have hE : ¬ ∃ YL : ℕ, (YL : ℤ) ≡ (a : ℤ) [ZMOD M] ∧
        rootCellCode S (YL : ℝ) = rootCellCode S (XL : ℝ) ∧
        T.ArithmeticSupport value childBound pivotBound YL XR := by
      rintro ⟨YL, hresY, hcode, hY⟩
      have ht := moving_top_support_cells value hvalue childBound pivotBound T hf YL XL XR
        ((hresY.trans hres.symm).of_dvd (by exact_mod_cast hM))
        (rootCellCode_eq_of_subset _ S hS _ _ hcode)
      exact hX (ht.mp hY)
    rw [ite_eq_right hX, dite_eq_right hE, zero_mul]

theorem movingSupportedPrimeInterval_cells {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M : ℕ)
    (S : Finset ℝ) (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hS : movingTopRootCuts value hvalue childBound pivotBound T hf XR ⊆ S)
    (w : ℕ → ℂ)
    (hw : ∀ XL YL, T.ArithmeticSupport value childBound pivotBound XL XR →
      T.ArithmeticSupport value childBound pivotBound YL XR →
      (XL : ℤ) ≡ (YL : ℤ) [ZMOD M] →
      rootCellCode S (XL : ℝ) = rootCellCode S (YL : ℝ) → w XL = w YL)
    (u v : ℝ) (f : ℝ → ℂ) :
    complexPrimeInterval M a u v (fun y =>
      (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
        w ⌊Real.exp y⌋₊) * f y) =
    complexPrimeInterval M a u v (fun y =>
      movingSupportedCellValue value childBound pivotBound T XR a M S w
        (rootCellCode S (Real.exp y)) * f y) := by
  apply complexPrimeInterval_congr
  intro p hp hprime hpa
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  rw [Real.exp_log hp0, Nat.floor_natCast]
  rw [movingSupportedCellValue_eq value hvalue childBound pivotBound T hf XR a M S hM hS
    w hw p (Int.natCast_modEq_iff.mpr hpa)]

/-- The original gate times a residue weight is compared without deleting
boundary primes or changing the retained Page density. -/
theorem PublishedProgressionInput.moving_supported_prime_comparison
    (P : PublishedProgressionInput) {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M Q : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hQ : 2 ≤ Q) (hq : 1 ≤ M) (hqQ : M ≤ Q) (ha : a.Coprime M)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
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
      ‖complexPrimeInterval M a u v (fun y =>
          (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
            w ⌊Real.exp y⌋₊) * smoothPolynomialWeight F (Real.exp y)) -
        ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
          d j * smoothPolynomialWeight F (Real.exp y) *
            (selectedPrimeLogDensity P Q M a y : ℂ)‖ ≤
        ∑ j ∈ Finset.range N,
          (‖d j‖ * smoothPolynomialBudget F *
            (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
              Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
            2 * B * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  obtain ⟨s, N, d, hs, hs0, hsN, hN, hd, herr⟩ := P.root_cell_prime_comparison hQ hq hqQ ha
    u v hu huv hshort F S hroots
    (movingSupportedCellValue value childBound pivotBound T XR a M S w) B hB
    (movingSupportedCellValue_norm value childBound pivotBound T XR a M S w B hB hwB)
  refine ⟨s, N, d, hs, hs0, hsN, hN, hd, ?_⟩
  rw [movingSupportedPrimeInterval_cells value hvalue childBound pivotBound T hf XR a M S
    hM hS w hw]
  exact herr

end Ostmann

end OAI

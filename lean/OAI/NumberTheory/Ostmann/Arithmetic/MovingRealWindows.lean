import OAI.NumberTheory.Ostmann.Arithmetic.MovingWindowedSpectators
import OAI.NumberTheory.Ostmann.Arithmetic.MovingResidueFactorization
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLogLeaves

namespace OAI

/-! # The terminal-window factor on two real giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotData.leafPolynomials_real {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (z : ℝ) (i : TreeLeafIndex n) :
    (T.leafPolynomials value L R i).eval z = T.realLeafModuli value (L.eval z) (R.eval z) i := by
  induction T generalizing L R with
  | leaf => simp only [leafPolynomials, realLeafModuli, Polynomial.eval_mul, Polynomial.eval_C]
  | node s CL CR U left right ihL ihR =>
    cases i with
    | inl i =>
      simpa only [leafPolynomials, realLeafModuli, MovingSlotReversal.pivotPolynomial_eval] using
        ihL ((MovingSlotData.step s CL CR U left right false).pivotPolynomial value L R) L i
    | inr i =>
      simpa only [leafPolynomials, realLeafModuli, MovingSlotReversal.pivotPolynomial_eval] using
        ihR ((MovingSlotData.step s CL CR U left right false).pivotPolynomial value L R) R i

theorem MovingSlotData.realLeafModuli_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (hI : T.Integral value XL XR) (i : TreeLeafIndex n) :
    T.realLeafModuli value XL XR i = (T.leafModuli value XL XR i : ℝ) := by
  have h := T.leafPolynomials_real value Polynomial.X (Polynomial.C XR) XL i
  rw [T.leafPolynomials_eval value hvalue hf XL XR hI _ _ _ (by simp) (by simp) i] at h
  simpa only [Polynomial.eval_X, Polynomial.eval_C] using h.symm

noncomputable def movingRealWindowFlag {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (X lo hi XL XR : ℝ) : ℂ :=
  if ∀ i, T.realLeafModuli value XL XR i / X ∈ Set.Icc lo hi then 1 else 0

theorem movingWindowedData_real_factor {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) :
    movingUnrestrictedWeight value (movingWindowLeaf value X lo hi (movingDataLeaf F))
      (movingDataExtra E) T XL XR =
        movingRealWindowFlag value T X lo hi XL XR * movingDataWeight F E T := by
  rw [movingUnrestrictedWeight_data_window]
  simp only [movingRealWindowFlag, T.realLeafModuli_nat value hvalue hf XL XR hI]
  split_ifs <;> simp only [one_mul, zero_mul]

/-- The original nonsmooth coefficient is exactly a fixed residue factor
times a function of the two real giant coordinates. This includes zero terms. -/
theorem moving_original_nonsmooth_residue_factor {σ I : Type*} (q : I → ℕ)
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
      (movingResidueFlag nodes (topGiantInput a b) * movingSpectatorResidue q value g D S T a b) *
        (movingArchimedeanFlag nodes (topGiantReal XL XR) *
          movingRealWindowFlag value T X lo hi XL XR * movingDataWeight F E T) := by
  dsimp only
  have he : movingArithmeticIndicator value childBound pivotBound T XL XR *
        movingWindowedSpectatorWeight q value F E X lo hi g D S T XL XR =
      (movingArithmeticIndicator value childBound pivotBound T XL XR *
        ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR) *
        (movingRealWindowFlag value T X lo hi XL XR * movingDataWeight F E T) := by
    by_cases hs : T.ArithmeticSupport value childBound pivotBound XL XR
    · unfold movingWindowedSpectatorWeight
      rw [movingWindowedData_real_factor value hvalue F E X lo hi T hf XL XR
        (hs.integral value hvalue childBound pivotBound T XL XR)]
      ring
    · have hz : movingArithmeticIndicator value childBound pivotBound T XL XR = 0 := ite_eq_right hs
      rw [hz, zero_mul, zero_mul, zero_mul]
  rw [he, moving_arithmetic_spectator_residue_factor q value hvalue childBound pivotBound
    g D S T hf XL XR a b M hM hMq hL hR]
  ring

end Ostmann

end OAI

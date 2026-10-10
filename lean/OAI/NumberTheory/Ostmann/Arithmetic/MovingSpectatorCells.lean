import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCongruence
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedCells
import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticPrimeComparison

namespace OAI

/-! # The original spectator product inside the prime-cell comparison -/

namespace Ostmann
open scoped Classical BigOperators
open MeasureTheory

theorem movingSpectatorProduct_modEq {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (M XL XR YL : ℕ)
    (hM : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hX : T.Integral value XL XR) (hY : T.Integral value YL XR)
    (hres : (XL : ℤ) ≡ (YL : ℤ) [ZMOD M]) :
    (∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR) =
      ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T YL XR := by
  apply Finset.prod_congr rfl
  intro i hi
  exact movingSlotSpectator_modEq value hvalue (g i) (D i) T hf XL XR YL XR hX hY
    (hres.of_dvd (hM i hi)) (Int.ModEq.refl _)

theorem movingSpectatorProduct_norm {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i)
    (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    ‖∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR‖ ≤
      ∏ i ∈ S, B i ^ (2 ^ n) := by
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    exact movingSlotSpectator_norm value (g i) (D i) (B i) (hB i hi) (hg i hi) T XL XR

/-- This is the literal moving spectator recursion under the original
arithmetic indicator. Its residue constancy is proved above; it is not an
extra input to the prime comparison. -/
theorem PublishedProgressionInput.moving_spectator_prime_comparison
    (P : PublishedProgressionInput) {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M Q : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hQ : 2 ≤ Q) (hq : 1 ≤ M) (hqQ : M ≤ Q) (ha : a.Coprime M)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) :
    ∃ (s : ℕ → ℝ) (N : ℕ) (d : ℕ → ℂ),
      Monotone s ∧ s 0 = u ∧ s N = v ∧
      N ≤ (movingTopRootCuts value hvalue childBound pivotBound T hf XR).card +
        (∑ i, (F i).polynomial.derivative.natDegree) + 1 ∧
      (∀ j, ‖d j‖ ≤ ∏ i ∈ S, B i ^ (2 ^ n)) ∧
      ‖complexPrimeInterval M a u v (fun y =>
          (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
            ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T ⌊Real.exp y⌋₊ XR) *
              smoothPolynomialWeight F (Real.exp y)) -
        ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
          d j * smoothPolynomialWeight F (Real.exp y) *
            (selectedPrimeLogDensity P Q M a y : ℂ)‖ ≤
        ∑ j ∈ Finset.range N,
          (‖d j‖ * smoothPolynomialBudget F *
            (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
              Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
            2 * (∏ i ∈ S, B i ^ (2 ^ n)) * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  let roots := movingPrimeRootCuts value hvalue childBound pivotBound T hf XR F
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
  obtain ⟨s, N, d, hs, hs0, hsN, hN, hd, herr⟩ := P.moving_supported_prime_comparison
    value hvalue childBound pivotBound T hf XR a M Q hM hQ hq hqQ ha u v hu huv hshort
    F roots hS hroots (fun XL => ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR)
    (∏ i ∈ S, B i ^ (2 ^ n)) hprod
    (fun XL _ => movingSpectatorProduct_norm q value g D S B hB hg T XL XR)
    (fun XL YL hX hY hres _ => movingSpectatorProduct_modEq q value hvalue g D S T hf
      M XL XR YL hMq (hX.integral value hvalue childBound pivotBound T XL XR)
      (hY.integral value hvalue childBound pivotBound T YL XR) hres)
  exact ⟨s, N, d, hs, hs0, hsN, hN.trans
    (Nat.add_le_add_right (movingPrimeRootCuts_card value hvalue childBound pivotBound T hf XR F) 1),
    hd, herr⟩

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.MovingCanonicalWeights
import OAI.NumberTheory.Ostmann.Arithmetic.RootMeshIntegral

namespace OAI

/-! # The original moving coefficient on a common residue-independent mesh -/

namespace Ostmann
open scoped Classical BigOperators
open MeasureTheory

section
variable {σ I : Type*} (q : I → ℕ) [∀ i, Fact (q i).Prime]
  (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
  (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
  (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
  (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
  (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
  {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
  (XR a b M : ℕ)

local notation "nodes" => T.formulaNodes value hvalue childBound pivotBound hf (HistoryFormula.prime false) (HistoryFormula.prime true)
local notation "coef" => movingResidueCoefficient q value F E g D S T nodes a b
local notation "profile" => fun x => movingRealGateWeight value T nodes X lo hi (topGiantReal x XR)
local notation "w" => fun x => coef * profile x
local notation "C" => ‖movingDataWeight F E T‖ * ∏ i ∈ S, B i ^ (2 ^ n)

include hB hg in
theorem moving_canonical_profile_bound (x : ℝ) : ‖w x‖ ≤ C := by
  rw [norm_mul]
  have hc := movingResidueCoefficient_norm q value F E g D S B hB hg T nodes a b
  calc
    _ ≤ C * 1 := mul_le_mul hc (movingRealGateWeight_norm value T nodes X lo hi _)
      (norm_nonneg _) (mul_nonneg (norm_nonneg _)
        (Finset.prod_nonneg fun i hi => pow_nonneg (hB i hi) _))
    _ = _ := mul_one _

theorem moving_canonical_profile_cell (roots : Finset ℝ)
    (hS : movingRealRootCuts value T nodes X lo hi false XR ⊆ roots)
    (x y : ℝ) (hcode : rootCellCode roots x = rootCellCode roots y) : w x = w y := by
  have he := movingRealGateWeight_rootCell value T nodes X lo hi false XR x y roots hS hcode
  change profile x = profile y at he
  exact congrArg (coef * ·) he

include hB hg in
/-- The same supplied mesh works for every admissible residue pair. Its
cell multiplier is the literal residue coefficient times the real midpoint gate. -/
theorem PublishedProgressionInput.moving_canonical_prime_integral
    (P : PublishedProgressionInput)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) (Q : ℕ)
    (hQ : 2 ≤ Q) (hq : 1 ≤ M) (hqQ : M ≤ Q) (ha : a.Coprime M)
    (roots : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hu : 1 ≤ s 0) (hshort : s N ≤ s 0 + 1)
    (hfree : ∀ j < N, ∀ r ∈ roots, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (hS : movingRealRootCuts value T nodes X lo hi false XR ⊆ roots)
    {k : ℕ} (W : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (W i).polynomial.derivative.roots → r ∈ roots) :
    ‖complexPrimeInterval M a (s 0) (s N) (fun y =>
        (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
          movingWindowedSpectatorWeight q value F E X lo hi g D S T ⌊Real.exp y⌋₊ XR) *
            smoothPolynomialWeight W (Real.exp y)) -
      ∫ y in Set.Ioc (s 0) (s N),
        w (Real.exp y) * smoothPolynomialWeight W (Real.exp y) * (selectedPrimeLogDensity P Q M a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget W *
          (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
            Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
          2 * C * smoothPolynomialBudget W * Real.exp (-(s j))) := by
  rw [moving_canonical_prime_interval q value hvalue childBound pivotBound F E X lo hi
    g D S T hf XR a b M hM hMq hR]
  exact P.common_root_prime_integral roots s hs N hfree hQ hq hqQ ha hu hshort W hroots
    w C (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i hi => pow_nonneg (hB i hi) _))
    (moving_canonical_profile_bound q value hvalue childBound pivotBound F E X lo hi g D S B hB hg T hf XR a b)
    (moving_canonical_profile_cell q value hvalue childBound pivotBound F E X lo hi g D S T hf XR a b roots hS)

include hB hg in
theorem moving_canonical_integer_integral
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) (hq : 0 < M) (G : ℝ)
    (roots : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ roots, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (hS : movingRealRootCuts value T nodes X lo hi false XR ⊆ roots)
    {k : ℕ} (W : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (W i).polynomial.derivative.roots → r ∈ roots) :
    ‖complexIntegerInterval M a (s 0) (s N) G (fun y =>
        (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
          movingWindowedSpectatorWeight q value F E X lo hi g D S T ⌊Real.exp y⌋₊ XR) *
            smoothPolynomialWeight W (Real.exp y)) -
      ∫ y in Set.Ioc (s 0) (s N),
        w (Real.exp y) * smoothPolynomialWeight W (Real.exp y) * (integerLogDensity M G y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget W *
          (2 * Real.exp (-G)) + 2 * C * smoothPolynomialBudget W * Real.exp (-G)) := by
  rw [moving_canonical_integer_interval q value hvalue childBound pivotBound F E X lo hi
    g D S T hf XR a b M hM hMq hR]
  exact common_root_integer_integral roots s hs N hfree M a hq G W hroots
    w C (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i hi => pow_nonneg (hB i hi) _))
    (moving_canonical_profile_bound q value hvalue childBound pivotBound F E X lo hi g D S B hB hg T hf XR a b)
    (moving_canonical_profile_cell q value hvalue childBound pivotBound F E X lo hi g D S T hf XR a b roots hS)

end
end Ostmann

end OAI

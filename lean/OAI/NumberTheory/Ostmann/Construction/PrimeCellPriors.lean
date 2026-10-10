import OAI.NumberTheory.Ostmann.Arithmetic.WeightedPrimeIntervals
import OAI.NumberTheory.Ostmann.ZeroDensity.UniformPrimeProgressions
import OAI.NumberTheory.Ostmann.Construction.FiniteCellPrior

namespace OAI

/-! # Cell masses of the actual weighted prime samples

The fiber identity specifies a finite log/residue partition. The sampling
weight is the original reciprocal-prime weight, not an abstract nearby
distribution. Its comparison with the retained Page density is derived
from the published progression inputs.
-/

namespace Ostmann

open scoped BigOperators Classical
open MeasureTheory

noncomputable def primeSamplePrior (S : Finset ℕ) (w : ℝ → ℝ) (Z : ℝ) (p : S) : ℝ :=
  Z * (w (Real.log (p : ℕ)) * ((p : ℕ) : ℝ)⁻¹)

theorem primeSamplePrior_nonneg (S : Finset ℕ) (w : ℝ → ℝ) (Z : ℝ)
    (hZ : 0 ≤ Z) (hw : ∀ p ∈ S, 0 ≤ w (Real.log p)) (p : S) :
    0 ≤ primeSamplePrior S w Z p :=
  mul_nonneg hZ (mul_nonneg (hw p p.property) (by positivity))

theorem primeSamplePrior_mass (S : Finset ℕ) (w : ℝ → ℝ) (Z : ℝ) :
    (∑ p : S, primeSamplePrior S w Z p) =
      Z * ∑ p ∈ S, w (Real.log p) * (p : ℝ)⁻¹ := by
  simp only [primeSamplePrior, ← Finset.mul_sum]
  rw [Finset.sum_coe_sort S (fun p : ℕ => w (Real.log p) * (p : ℝ)⁻¹)]

theorem primeSamplePrior_normalized (S : Finset ℕ) (w : ℝ → ℝ)
    (hmass : (∑ p ∈ S, w (Real.log p) * (p : ℝ)⁻¹) ≠ 0) :
    (∑ p : S, primeSamplePrior S w
      (∑ p ∈ S, w (Real.log p) * (p : ℝ)⁻¹)⁻¹ p) = 1 := by
  rw [primeSamplePrior_mass, inv_mul_cancel₀ hmass]

/-- Exact identification of a cell of the original prime sample. -/
theorem primeSamplePrior_cell {C : Type*}
    (S : Finset ℕ) (w : ℝ → ℝ) (Z : ℝ) (cell : ℕ → C) (c : C)
    (q a : ℕ) (s t : ℝ)
    (hfiber : S.filter (fun p => cell p = c) =
      (Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter
        (fun p => p.Prime ∧ Nat.ModEq q p a)) :
    cellPrior (primeSamplePrior S w Z) (fun p => cell p) c =
      Z * weightedReciprocalPrimeInterval q a s t w := by
  classical
  unfold cellPrior primeSamplePrior
  change (∑ p : S, if cell (p : ℕ) = c then
    Z * (w (Real.log (p : ℕ)) * ((p : ℕ) : ℝ)⁻¹) else 0) = _
  rw [Finset.sum_coe_sort S (fun p : ℕ =>
    if cell p = c then Z * (w (Real.log p) * (p : ℝ)⁻¹) else 0)]
  rw [← Finset.sum_filter, hfiber]
  rw [Finset.sum_filter]
  unfold weightedReciprocalPrimeInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.Prime ∧ Nat.ModEq q p a <;> simp [h]

/-- A concrete per-cell comparison, including normalization and the
cutoff variation. Only the cited theta/Page input is unproved. -/
theorem PublishedProgressionInput.primeSamplePrior_cell_error
    (P : PublishedProgressionInput) {C : Type*}
    (S : Finset ℕ) (w : ℝ → ℝ) (Z : ℝ) (hZ : 0 ≤ Z) (cell : ℕ → C) (c : C)
    {q Q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1)
    (hfiber : S.filter (fun p => cell p = c) =
      (Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter
        (fun p => p.Prime ∧ Nat.ModEq q p a))
    (hwc : ContinuousOn w (Set.Icc s t)) (w₀ η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc s t, |w y - w₀| ≤ η) :
    |cellPrior (primeSamplePrior S w Z) (fun p => cell p) c -
      Z * ∫ y in Set.Ioc s t, w y * primeLogDensity (Nat.totient q)
        (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
        (pageBeta (pageAtModulus q (selectedPageZero P Q))) y| ≤
      Z * ((|w₀| + η) *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) +
          Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ)))) + 4 * η) := by
  rw [primeSamplePrior_cell S w Z cell c q a s t hfiber, ← mul_sub,
    abs_mul, abs_of_nonneg hZ]
  apply mul_le_mul_of_nonneg_left _ hZ
  apply weighted_prime_log_interval_error q a _ _ _
    (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q))
    (pageCoefficient_abs_le_one _ _) (pageBeta_le_one _)
    hs hst hshort w hwc w₀ η _ hη hw
  exact P.uniform_log_interval hQ hq hqQ ha hs hst hshort

end Ostmann

end OAI

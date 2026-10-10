import OAI.NumberTheory.Ostmann.Construction.PrimeCellPriors

namespace OAI

/-! # Joint idealization of actual cutoff-weighted prime samples

The only analytic input is `PublishedProgressionInput`. Partition fibers,
cutoff variation, and the final numerical error budget are explicit. The
ideal masses are the integrals with the retained Page correction.
-/

namespace Ostmann

open scoped BigOperators Classical
open MeasureTheory

structure PrimeCellPartition (S : Finset ℕ) (C : Type*) where
  modulus : ℕ
  modulus_pos : 1 ≤ modulus
  cell : ℕ → C
  residue : C → ℕ
  lower : C → ℝ
  upper : C → ℝ
  lower_one : ∀ c, 1 ≤ lower c
  ordered : ∀ c, lower c ≤ upper c
  short : ∀ c, upper c ≤ lower c + 1
  coprime : ∀ c, (residue c).Coprime modulus
  fiber : ∀ c, S.filter (fun p => cell p = c) =
    (Finset.Ioc ⌊Real.exp (lower c)⌋₊ ⌊Real.exp (upper c)⌋₊).filter
      (fun p => p.Prime ∧ Nat.ModEq modulus p (residue c))

noncomputable def idealPrimeCellPrior (P : PublishedProgressionInput) (Q : ℕ)
    {S : Finset ℕ} {C : Type*} (D : PrimeCellPartition S C)
    (w : ℝ → ℝ) (Z : ℝ) (c : C) : ℝ :=
  Z * ∫ y in Set.Ioc (D.lower c) (D.upper c),
    w y * primeLogDensity (Nat.totient D.modulus)
      (pageCoefficient (pageAtModulus D.modulus (selectedPageZero P Q)) (D.residue c))
      (pageBeta (pageAtModulus D.modulus (selectedPageZero P Q))) y

theorem idealPrimeCellPrior_nonneg (P : PublishedProgressionInput) (Q : ℕ)
    {S : Finset ℕ} {C : Type*} (D : PrimeCellPartition S C)
    (w : ℝ → ℝ) (Z : ℝ) (hZ : 0 ≤ Z)
    (hw : ∀ c y, y ∈ Set.Ioc (D.lower c) (D.upper c) → 0 ≤ w y) (c : C) :
    0 ≤ idealPrimeCellPrior P Q D w Z c := by
  apply mul_nonneg hZ
  apply setIntegral_nonneg measurableSet_Ioc
  intro y hy
  apply mul_nonneg (hw c y hy)
  exact (primeLogDensity_bounds _ _ _ (Nat.cast_nonneg _)
    (pageCoefficient_abs_le_one _ _) (pageBeta_le_one _)
    (by linarith [D.lower_one c, hy.1])).1

/-- A signed complex joint statistic of independent original prime samples
is compared with the product of their explicit Page-corrected cell priors.
No conditional equidistribution or ideal-mass assumption is needed. -/
theorem PublishedProgressionInput.prime_cell_idealization
    (P : PublishedProgressionInput) (Q : ℕ) (hQ : 2 ≤ Q)
    (S : Finset ℕ) {C : Type*} [Fintype C] {n : ℕ}
    (D : Fin n → PrimeCellPartition S C) (hmod : ∀ i, (D i).modulus ≤ Q)
    (w : Fin n → ℝ → ℝ) (Z : Fin n → ℝ) (hZ : ∀ i, 0 ≤ Z i)
    (hw : ∀ i p, p ∈ S → 0 ≤ w i (Real.log p))
    (hwi : ∀ i c y, y ∈ Set.Ioc ((D i).lower c) ((D i).upper c) → 0 ≤ w i y)
    (hmass : ∀ i, Z i * (∑ p ∈ S, w i (Real.log p) * (p : ℝ)⁻¹) ≤ 1)
    (hwc : ∀ i c, ContinuousOn (w i) (Set.Icc ((D i).lower c) ((D i).upper c)))
    (w₀ : Fin n → C → ℝ) (ηw δ B η : ℝ)
    (hηw : 0 ≤ ηw) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hvariation : ∀ i c y, y ∈ Set.Ioc ((D i).lower c) ((D i).upper c) →
      |w i y - w₀ i c| ≤ ηw)
    (hbudget : ∀ i c, Z i * ((|w₀ i c| + ηw) *
      (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt ((D i).lower c)) +
        Real.exp (-P.kappa * (D i).lower c / Real.log (4 * (Q : ℝ)))) + 4 * ηw) ≤ δ)
    (hsmall : Fintype.card C * δ ≤ 1)
    (H : (Fin n → S) → ℂ) (F : (Fin n → C) → ℂ)
    (hF : ∀ y, ‖F y‖ ≤ B)
    (hfreeze : ∀ x, ‖H x - F (fun i => (D i).cell (x i))‖ ≤ η) :
    ‖(∑ x, (productPrior (fun i => primeSamplePrior S (w i) (Z i)) x : ℂ) * H x) -
      (∑ y, (productPrior (fun i => idealPrimeCellPrior P Q (D i) (w i) (Z i)) y : ℂ) * F y)‖ ≤
        η * 2 ^ n + B * n * (Fintype.card C * δ) * 2 ^ n := by
  apply finite_cell_idealization_of_probability
    (fun i => primeSamplePrior S (w i) (Z i)) (fun i p => (D i).cell p)
    (fun i => idealPrimeCellPrior P Q (D i) (w i) (Z i))
    (fun i p => primeSamplePrior_nonneg S (w i) (Z i) (hZ i) (hw i) p)
    (fun i c => idealPrimeCellPrior_nonneg P Q (D i) (w i) (Z i) (hZ i) (hwi i) c)
    (fun i => by rw [primeSamplePrior_mass]; exact hmass i)
    δ B η hδ hB hη hsmall _ H F hF hfreeze
  intro i c
  exact (P.primeSamplePrior_cell_error S (w i) (Z i) (hZ i) (D i).cell c
    hQ (D i).modulus_pos (hmod i) ((D i).coprime c)
    ((D i).lower_one c) ((D i).ordered c) ((D i).short c) ((D i).fiber c)
    (hwc i c) (w₀ i c) ηw hηw (hvariation i c)).trans (hbudget i c)

end Ostmann

end OAI

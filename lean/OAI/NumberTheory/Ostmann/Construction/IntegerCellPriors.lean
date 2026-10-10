import OAI.NumberTheory.Ostmann.Arithmetic.WeightedIntegerIntervals
import OAI.NumberTheory.Ostmann.Construction.FiniteCellPrior

namespace OAI

/-! # Cells of the original external-integer sampling law -/

namespace Ostmann

open scoped BigOperators Classical
open MeasureTheory

noncomputable def integerSamplePrior (S : Finset ℕ) (w : ℝ → ℝ) (G Z : ℝ)
    (n : S) : ℝ := Z * Real.exp (-G) * w (Real.log (n : ℕ))

theorem integerSamplePrior_nonneg (S : Finset ℕ) (w : ℝ → ℝ) (G Z : ℝ)
    (hZ : 0 ≤ Z) (hw : ∀ n ∈ S, 0 ≤ w (Real.log n)) (n : S) :
    0 ≤ integerSamplePrior S w G Z n :=
  mul_nonneg (mul_nonneg hZ (Real.exp_pos _).le) (hw n n.property)

theorem integerSamplePrior_mass (S : Finset ℕ) (w : ℝ → ℝ) (G Z : ℝ) :
    (∑ n : S, integerSamplePrior S w G Z n) =
      Z * Real.exp (-G) * ∑ n ∈ S, w (Real.log n) := by
  simp only [integerSamplePrior, ← Finset.mul_sum]
  rw [Finset.sum_coe_sort S (fun n : ℕ => w (Real.log n))]

structure IntegerCellPartition (S : Finset ℕ) (C : Type*) where
  modulus : ℕ
  modulus_pos : 0 < modulus
  cell : ℕ → C
  residue : C → ℕ
  lower : C → ℝ
  upper : C → ℝ
  ordered : ∀ c, lower c ≤ upper c
  short : ∀ c, upper c ≤ lower c + 1
  fiber : ∀ c, S.filter (fun n => cell n = c) =
    (Finset.Ioc ⌊Real.exp (lower c)⌋₊ ⌊Real.exp (upper c)⌋₊).filter
      (fun n => Nat.ModEq modulus n (residue c))

theorem integerSamplePrior_cell {C : Type*}
    (S : Finset ℕ) (w : ℝ → ℝ) (G Z : ℝ) (D : IntegerCellPartition S C) (c : C) :
    cellPrior (integerSamplePrior S w G Z) (fun n => D.cell n) c =
      Z * weightedIntegerLogInterval D.modulus (D.residue c) (D.lower c) (D.upper c) G w := by
  unfold cellPrior integerSamplePrior
  change (∑ n : S, if D.cell (n : ℕ) = c then
    Z * Real.exp (-G) * w (Real.log (n : ℕ)) else 0) = _
  rw [Finset.sum_coe_sort S (fun n : ℕ =>
    if D.cell n = c then Z * Real.exp (-G) * w (Real.log n) else 0)]
  rw [← Finset.sum_filter, D.fiber c, Finset.sum_filter]
  unfold weightedIntegerLogInterval integerResidueAtom
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split <;> simp_all [mul_assoc]

noncomputable def idealIntegerCellPrior {S : Finset ℕ} {C : Type*}
    (D : IntegerCellPartition S C) (w : ℝ → ℝ) (G Z : ℝ) (c : C) : ℝ :=
  Z * ∫ y in Set.Ioc (D.lower c) (D.upper c), w y * integerLogDensity D.modulus G y

theorem idealIntegerCellPrior_nonneg {S : Finset ℕ} {C : Type*}
    (D : IntegerCellPartition S C) (w : ℝ → ℝ) (G Z : ℝ) (hZ : 0 ≤ Z)
    (hw : ∀ c y, y ∈ Set.Ioc (D.lower c) (D.upper c) → 0 ≤ w y) (c : C) :
    0 ≤ idealIntegerCellPrior D w G Z c := by
  apply mul_nonneg hZ
  apply setIntegral_nonneg measurableSet_Ioc
  intro y hy
  exact mul_nonneg (hw c y hy) (by unfold integerLogDensity; positivity)

theorem integerSamplePrior_cell_error {S : Finset ℕ} {C : Type*}
    (D : IntegerCellPartition S C) (w : ℝ → ℝ) (G Z : ℝ) (hZ : 0 ≤ Z) (c : C)
    (hwc : ContinuousOn w (Set.Icc (D.lower c) (D.upper c)))
    (w₀ η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc (D.lower c) (D.upper c), |w y - w₀| ≤ η) :
    |cellPrior (integerSamplePrior S w G Z) (fun n => D.cell n) c -
      idealIntegerCellPrior D w G Z c| ≤
      Z * ((|w₀| + η) * (2 * Real.exp (-G)) + 2 * η * Real.exp (D.upper c - G)) := by
  rw [integerSamplePrior_cell, idealIntegerCellPrior, ← mul_sub, abs_mul,
    abs_of_nonneg hZ]
  apply mul_le_mul_of_nonneg_left _ hZ
  exact weighted_integer_log_density_error D.modulus (D.residue c) D.modulus_pos
    (D.lower c) (D.upper c) G (D.ordered c) (D.short c) w hwc w₀ η hη hw

end Ostmann

end OAI

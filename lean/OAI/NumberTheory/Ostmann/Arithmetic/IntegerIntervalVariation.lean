import OAI.NumberTheory.Ostmann.Arithmetic.WeightedIntegerIntervals
import OAI.NumberTheory.Ostmann.Arithmetic.PrimePartitionVariation

namespace OAI

/-! # Abel variation for the original external integer measure -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

noncomputable def complexIntegerInterval (q a : ℕ) (u v G : ℝ) (w : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
    w (Real.log n) * (integerResidueAtom q a G n : ℂ)

theorem complexIntegerInterval_add (q a : ℕ) (u v t G : ℝ) (w : ℝ → ℂ)
    (huv : u ≤ v) (hvt : v ≤ t) :
    complexIntegerInterval q a u v G w + complexIntegerInterval q a v t G w =
      complexIntegerInterval q a u t G w :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

theorem integerLogCellMass_add (q a : ℕ) (u v t G : ℝ) (huv : u ≤ v) (hvt : v ≤ t) :
    integerLogCellMass q a u v G + integerLogCellMass q a v t G =
      integerLogCellMass q a u t G :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

theorem integerResidueAtom_nonneg (q a : ℕ) (G : ℝ) (n : ℕ) :
    0 ≤ integerResidueAtom q a G n := by
  unfold integerResidueAtom
  split_ifs <;> positivity

theorem integerLogCellMass_nonneg (q a : ℕ) (u v G : ℝ) :
    0 ≤ integerLogCellMass q a u v G :=
  Finset.sum_nonneg (fun _ _ => integerResidueAtom_nonneg _ _ _ _)

theorem continuous_integerLogDensity (q : ℕ) (G : ℝ) : Continuous (integerLogDensity q G) :=
  (Real.continuous_exp.comp (continuous_id.sub continuous_const)).div_const q

theorem complexIntegerInterval_freeze (q a : ℕ) (u v G : ℝ)
    (w : ℝ → ℂ) (c : ℂ) (η : ℝ)
    (hw : ∀ y ∈ Set.Ioc u v, ‖w y - c‖ ≤ η) :
    ‖complexIntegerInterval q a u v G w - c * (integerLogCellMass q a u v G : ℂ)‖ ≤
      η * integerLogCellMass q a u v G := by
  have heq : complexIntegerInterval q a u v G w - c * (integerLogCellMass q a u v G : ℂ) =
      ∑ n ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
        (w (Real.log n) - c) * (integerResidueAtom q a G n : ℂ) := by
    unfold complexIntegerInterval integerLogCellMass
    rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, η * integerResidueAtom q a G n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integerResidueAtom_nonneg q a G n)]
      exact mul_le_mul_of_nonneg_right (hw _ (log_mem_of_mem_exp_interval hn))
        (integerResidueAtom_nonneg q a G n)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem integerLogCellMass_partition (q a : ℕ) (G : ℝ) (s : ℕ → ℝ)
    (hs : Monotone s) (N : ℕ) :
    (∑ j ∈ Finset.range N, integerLogCellMass q a (s j) (s (j + 1)) G) =
      integerLogCellMass q a (s 0) (s N) G := by
  induction N with
  | zero => simp [integerLogCellMass]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    exact integerLogCellMass_add q a _ _ _ G (hs (Nat.zero_le _)) (hs (Nat.le_succ _))

theorem complexIntegerInterval_partition (q a : ℕ) (G : ℝ) (s : ℕ → ℝ)
    (hs : Monotone s) (w : ℝ → ℂ) (N : ℕ) :
    (∑ j ∈ Finset.range N, complexIntegerInterval q a (s j) (s (j + 1)) G w) =
      complexIntegerInterval q a (s 0) (s N) G w := by
  induction N with
  | zero => simp [complexIntegerInterval]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    exact complexIntegerInterval_add q a _ _ _ G w (hs (Nat.zero_le _)) (hs (Nat.le_succ _))

/-- The integer progression discrepancy pays total variation rather than
the number of intervals. The normalization remains the original exp(-G). -/
theorem weighted_integer_interval_variation (q a : ℕ) (hq : 0 < q) (G : ℝ)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) (w : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range N, w j *
      ((integerLogCellMass q a (s j) (s (j + 1)) G -
        ∫ y in Set.Ioc (s j) (s (j + 1)), integerLogDensity q G y : ℝ) : ℂ)‖ ≤
      discreteVariation w N * (2 * Real.exp (-G)) := by
  apply weighted_sum_le_variation
  intro k _
  rw [← Complex.ofReal_sum, Finset.sum_sub_distrib, integerLogCellMass_partition q a G s hs k,
    integral_Ioc_partition s hs k _ (continuous_integerLogDensity q G).continuousOn,
    Complex.norm_real, Real.norm_eq_abs]
  exact integerLogCellMass_error q a hq _ _ G (hs (Nat.zero_le _))

end Ostmann

end OAI

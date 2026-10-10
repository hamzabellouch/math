import OAI.NumberTheory.Ostmann.Construction.IntegerIntervalDistribution
import OAI.NumberTheory.Ostmann.Arithmetic.WeightedPrimeIntervals

namespace OAI

/-! # Cutoff-weighted distribution of the external integer coordinate -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

private theorem finite_weight_freeze {A : Type*} (S : Finset A)
    (μ w : A → ℝ) (w₀ η : ℝ) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hw : ∀ a ∈ S, |w a - w₀| ≤ η) :
    |(∑ a ∈ S, μ a * w a) - w₀ * ∑ a ∈ S, μ a| ≤ η * ∑ a ∈ S, μ a := by
  have heq : (∑ a ∈ S, μ a * w a) - w₀ * ∑ a ∈ S, μ a =
      ∑ a ∈ S, μ a * (w a - w₀) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq, ← Real.norm_eq_abs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ S, μ a * η := Finset.sum_le_sum fun a ha => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hμ a ha), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hw a ha) (hμ a ha)
    _ = _ := by rw [← Finset.sum_mul]; ring

noncomputable def integerResidueAtom (q a : ℕ) (G : ℝ) (n : ℕ) : ℝ :=
  if Nat.ModEq q n a then Real.exp (-G) else 0

noncomputable def integerLogCellMass (q a : ℕ) (s t G : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊, integerResidueAtom q a G n

noncomputable def weightedIntegerLogInterval (q a : ℕ) (s t G : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊, integerResidueAtom q a G n * w (Real.log n)

theorem integerLogCellMass_eq (q a : ℕ) (s t G : ℝ) :
    integerLogCellMass q a s t G = Real.exp (-G) *
      (((Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ) := by
  unfold integerLogCellMass integerResidueAtom
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem integerLogCellMass_error (q a : ℕ) (hq : 0 < q)
    (s t G : ℝ) (hst : s ≤ t) :
    |integerLogCellMass q a s t G - ∫ y in Set.Ioc s t, integerLogDensity q G y| ≤
      2 * Real.exp (-G) := by
  rw [integerLogCellMass_eq]
  exact integer_log_density_error q a hq s t G hst

theorem weightedIntegerLogInterval_freeze (q a : ℕ) (s t G : ℝ)
    (w : ℝ → ℝ) (w₀ η : ℝ) (hw : ∀ y ∈ Set.Ioc s t, |w y - w₀| ≤ η) :
    |weightedIntegerLogInterval q a s t G w - w₀ * integerLogCellMass q a s t G| ≤
      η * integerLogCellMass q a s t G := by
  apply finite_weight_freeze
  · intro n _
    unfold integerResidueAtom
    split <;> positivity
  · intro n hn
    exact hw _ (log_mem_of_mem_exp_interval hn)

theorem integerLogDensity_abs_le (q : ℕ) (hq : 0 < q) (G : ℝ) {y t : ℝ} (hyt : y ≤ t) :
    |integerLogDensity q G y| ≤ Real.exp (t - G) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  unfold integerLogDensity
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_self (Real.exp_pos _).le hq1).trans
    (Real.exp_le_exp.mpr (sub_le_sub_right hyt G))

theorem integerLogDensity_integral_abs_le (q : ℕ) (hq : 0 < q) (s t G : ℝ)
    (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |∫ y in Set.Ioc s t, integerLogDensity q G y| ≤ Real.exp (t - G) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := Real.exp (t - G)) (f := integerLogDensity q G)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      exact integerLogDensity_abs_le q hq G (((Set.uIoc_of_le hst) ▸ hy).2))
  rw [intervalIntegral.integral_of_le hst, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at h
  exact h.trans (by nlinarith [Real.exp_pos (t - G)])

theorem integerLogDensity_integral_freeze (q : ℕ) (hq : 0 < q) (s t G : ℝ)
    (hst : s ≤ t) (hshort : t ≤ s + 1)
    (w : ℝ → ℝ) (hwc : ContinuousOn w (Set.Icc s t)) (w₀ η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc s t, |w y - w₀| ≤ η) :
    |(∫ y in Set.Ioc s t, w y * integerLogDensity q G y) -
      w₀ * (∫ y in Set.Ioc s t, integerLogDensity q G y)| ≤ η * Real.exp (t - G) := by
  have hc : ContinuousOn (integerLogDensity q G) (Set.Icc s t) :=
    ((Real.continuous_exp.comp (continuous_id.sub continuous_const)).div_const q).continuousOn
  have hiw : IntegrableOn (fun y => w y * integerLogDensity q G y) (Set.Ioc s t) :=
    (hwc.mul hc).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hic : IntegrableOn (fun y => w₀ * integerLogDensity q G y) (Set.Ioc s t) :=
    (continuousOn_const.mul hc).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have heq : (∫ y in Set.Ioc s t, w y * integerLogDensity q G y) -
      w₀ * (∫ y in Set.Ioc s t, integerLogDensity q G y) =
      ∫ y in Set.Ioc s t, (w y - w₀) * integerLogDensity q G y := by
    rw [← integral_const_mul, ← integral_sub hiw hic]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y _
    ring
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := η * Real.exp (t - G))
    (f := fun y => (w y - w₀) * integerLogDensity q G y)
    (fun y hy => by
      have hy' := (Set.uIoc_of_le hst) ▸ hy
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hw y hy') (integerLogDensity_abs_le q hq G hy'.2)
        (abs_nonneg _) hη)
  rw [intervalIntegral.integral_of_le hst, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at h
  exact h.trans (by
    have hM : 0 ≤ η * Real.exp (t - G) := mul_nonneg hη (Real.exp_pos _).le
    exact mul_le_of_le_one_right hM (by linarith))

/-- The integer analogue of the weighted prime progression estimate. -/
theorem weighted_integer_log_density_error (q a : ℕ) (hq : 0 < q) (s t G : ℝ)
    (hst : s ≤ t) (hshort : t ≤ s + 1)
    (w : ℝ → ℝ) (hwc : ContinuousOn w (Set.Icc s t)) (w₀ η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc s t, |w y - w₀| ≤ η) :
    |weightedIntegerLogInterval q a s t G w -
      ∫ y in Set.Ioc s t, w y * integerLogDensity q G y| ≤
      (|w₀| + η) * (2 * Real.exp (-G)) + 2 * η * Real.exp (t - G) := by
  let S := integerLogCellMass q a s t G
  let I := ∫ y in Set.Ioc s t, integerLogDensity q G y
  let W := weightedIntegerLogInterval q a s t G w
  let J := ∫ y in Set.Ioc s t, w y * integerLogDensity q G y
  have hbare := integerLogCellMass_error q a hq s t G hst
  have hS : S ≤ 2 * Real.exp (-G) + Real.exp (t - G) := by
    have hI := integerLogDensity_integral_abs_le q hq s t G hst hshort
    have hbare' := (le_abs_self _).trans hbare
    have hI' := (le_abs_self _).trans hI
    dsimp [S, I] at *
    linarith
  have hfreeze := weightedIntegerLogInterval_freeze q a s t G w w₀ η hw
  have hweighted := integerLogDensity_integral_freeze q hq s t G hst hshort w hwc w₀ η hη hw
  have hscale : |w₀ * S - w₀ * I| ≤ |w₀| * (2 * Real.exp (-G)) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hbare (abs_nonneg _)
  have h₁ := norm_sub_le_norm_sub_add_norm_sub W (w₀ * S) (w₀ * I)
  have h₂ := norm_sub_le_norm_sub_add_norm_sub W (w₀ * I) J
  simp only [Real.norm_eq_abs] at h₁ h₂
  have hweighted' : |w₀ * I - J| ≤ η * Real.exp (t - G) := by
    rw [abs_sub_comm]
    exact hweighted
  have hηS := mul_le_mul_of_nonneg_left hS hη
  dsimp [S, I, W, J] at *
  nlinarith

end Ostmann

end OAI

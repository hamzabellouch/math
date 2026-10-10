import OAI.NumberTheory.Ostmann.Arithmetic.PrimeIntervalVariation
import OAI.NumberTheory.Ostmann.Arithmetic.WeightedPrimeIntervals

namespace OAI

/-! # Complex smooth weights on actual prime intervals -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

noncomputable def complexPrimeInterval (q a : ℕ) (s t : ℝ) (w : ℝ → ℂ) : ℂ :=
  ∑ p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
    if p.Prime ∧ Nat.ModEq q p a then w (Real.log p) * ((p : ℝ)⁻¹ : ℂ) else 0

theorem complexPrimeInterval_add (q a : ℕ) (u v t : ℝ) (w : ℝ → ℂ)
    (huv : u ≤ v) (hvt : v ≤ t) :
    complexPrimeInterval q a u v w + complexPrimeInterval q a v t w =
      complexPrimeInterval q a u t w :=
  Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (Real.exp_le_exp.mpr huv))
    (Nat.floor_le_floor (Real.exp_le_exp.mpr hvt))

theorem complexPrimeInterval_freeze (q a : ℕ) (s t : ℝ) (w : ℝ → ℂ) (c : ℂ) (η : ℝ)
    (hw : ∀ y ∈ Set.Ioc s t, ‖w y - c‖ ≤ η) :
    ‖complexPrimeInterval q a s t w -
      c * (reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) : ℂ)‖ ≤
        η * reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) := by
  have heq : complexPrimeInterval q a s t w -
      c * (reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) : ℂ) =
      ∑ p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
        if p.Prime ∧ Nat.ModEq q p a then (w (Real.log p) - c) * ((p : ℝ)⁻¹ : ℂ) else 0 := by
    unfold complexPrimeInterval reciprocalPrimeInterval
    rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split <;> simp_all [sub_mul]
  rw [heq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
        η * (if p.Prime ∧ Nat.ModEq q p a then (p : ℝ)⁻¹ else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases h : p.Prime ∧ Nat.ModEq q p a
      · rw [ite_eq_left h, ite_eq_left h, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg p)]
        exact mul_le_mul_of_nonneg_right (hw _ (log_mem_of_mem_exp_interval hp)) (by positivity)
      · simp [h]
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Freezing a continuous complex weight costs its oscillation times the
length of the log interval. In particular the cost is additive over meshes. -/
theorem complex_density_integral_freeze (φ χ β s t : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) (hs : 1 ≤ s) (hst : s ≤ t)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc s t)) (c : ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc s t, ‖w y - c‖ ≤ η) :
    ‖(∫ y in Set.Ioc s t, w y * (primeLogDensity φ χ β y : ℂ)) -
      c * (∫ y in Set.Ioc s t, primeLogDensity φ χ β y : ℝ)‖ ≤ 2 * η * (t - s) := by
  have hc := continuousOn_primeLogDensity φ χ β (t := t) (by linarith : 0 < s)
  have hiw : IntegrableOn (fun y => w y * (primeLogDensity φ χ β y : ℂ)) (Set.Ioc s t) :=
    (hwc.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hic : IntegrableOn (fun y => c * (primeLogDensity φ χ β y : ℂ)) (Set.Ioc s t) :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have heq : (∫ y in Set.Ioc s t, w y * (primeLogDensity φ χ β y : ℂ)) -
      c * (∫ y in Set.Ioc s t, primeLogDensity φ χ β y : ℝ) =
      ∫ y in Set.Ioc s t, (w y - c) * (primeLogDensity φ χ β y : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul, ← integral_sub hiw hic]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y _
    ring
  rw [heq]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := 2 * η)
    (f := fun y => (w y - c) * (primeLogDensity φ χ β y : ℂ))
    (fun y hy => by
      have hy' := (Set.uIoc_of_le hst) ▸ hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hw y hy')
        (primeLogDensity_abs_le_two φ χ β hφ hχ hβ (hs.trans hy'.1.le))
        (abs_nonneg _) hη).trans_eq (mul_comm η 2))
  rwa [intervalIntegral.integral_of_le hst, abs_of_nonneg (sub_nonneg.mpr hst)] at hi

end Ostmann

end OAI

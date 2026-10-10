import OAI.NumberTheory.Ostmann.ZeroDensity.PrimeLogDensityBounds

namespace OAI

/-! # Freezing a smooth cutoff on an actual prime log cell -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

noncomputable def weightedReciprocalPrimeInterval (q a : ℕ) (s t : ℝ)
    (w : ℝ → ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
    if p.Prime ∧ Nat.ModEq q p a then w (Real.log p) * (p : ℝ)⁻¹ else 0

theorem log_mem_of_mem_exp_interval {p : ℕ} {s t : ℝ}
    (hp : p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊) :
    Real.log (p : ℝ) ∈ Set.Ioc s t := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp
  have hexp : Real.exp s < p := Nat.lt_of_floor_lt hlo
  have hp0 : (0 : ℝ) < p := (Real.exp_pos s).trans hexp
  exact ⟨(Real.lt_log_iff_exp_lt hp0).mpr hexp,
    (Real.log_le_iff_le_exp hp0).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp hhi)⟩

theorem reciprocalPrimeInterval_nonneg (q a : ℕ) (u v : ℝ) :
    0 ≤ reciprocalPrimeInterval q a u v := by
  apply Finset.sum_nonneg
  intro p _
  split <;> positivity

/-- Freezing uses the actual prime weights, with no equidistribution or
independence hypothesis. -/
theorem weightedReciprocalPrimeInterval_freeze (q a : ℕ) (s t : ℝ)
    (w : ℝ → ℝ) (w₀ η : ℝ)
    (hw : ∀ y ∈ Set.Ioc s t, |w y - w₀| ≤ η) :
    |weightedReciprocalPrimeInterval q a s t w -
      w₀ * reciprocalPrimeInterval q a (Real.exp s) (Real.exp t)| ≤
      η * reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) := by
  let S := Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊
  have heq : weightedReciprocalPrimeInterval q a s t w -
      w₀ * reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) =
      ∑ p ∈ S, if p.Prime ∧ Nat.ModEq q p a then
        (w (Real.log p) - w₀) * (p : ℝ)⁻¹ else 0 := by
    unfold weightedReciprocalPrimeInterval reciprocalPrimeInterval
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split <;> simp_all [sub_mul]
  rw [heq, ← Real.norm_eq_abs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ S, η * (if p.Prime ∧ Nat.ModEq q p a then (p : ℝ)⁻¹ else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases h : p.Prime ∧ Nat.ModEq q p a
      · rw [ite_eq_left h, ite_eq_left h, norm_mul, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (p : ℝ)⁻¹)]
        exact mul_le_mul_of_nonneg_right (hw _ (log_mem_of_mem_exp_interval hp))
          (inv_nonneg.mpr (Nat.cast_nonneg p))
      · simp [h]
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem primeLogDensity_abs_le_two (φ χ β : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    |primeLogDensity φ χ β y| ≤ 2 := by
  obtain ⟨hn, hu⟩ := primeLogDensity_bounds φ χ β (by linarith) hχ hβ (by linarith)
  rw [abs_of_nonneg hn]
  apply hu.trans
  exact div_le_self (by norm_num) (by nlinarith : (1 : ℝ) ≤ φ * y)

theorem primeLogDensity_integral_abs_le_two (φ χ β : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {s t : ℝ}
    (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |∫ y in Set.Ioc s t, primeLogDensity φ χ β y| ≤ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := (2 : ℝ)) (f := primeLogDensity φ χ β)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      exact primeLogDensity_abs_le_two φ χ β hφ hχ hβ
        (hs.trans (((Set.uIoc_of_le hst) ▸ hy).1.le)))
  rw [intervalIntegral.integral_of_le hst, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at h
  linarith

theorem primeLogDensity_integral_freeze (φ χ β : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {s t : ℝ}
    (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1)
    (w : ℝ → ℝ) (hwc : ContinuousOn w (Set.Icc s t)) (w₀ η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc s t, |w y - w₀| ≤ η) :
    |(∫ y in Set.Ioc s t, w y * primeLogDensity φ χ β y) -
      w₀ * (∫ y in Set.Ioc s t, primeLogDensity φ χ β y)| ≤ 2 * η := by
  have hc := continuousOn_primeLogDensity φ χ β (t := t) (lt_of_lt_of_le zero_lt_one hs)
  have hiw : IntegrableOn (fun y => w y * primeLogDensity φ χ β y) (Set.Ioc s t) :=
    (hwc.mul hc).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hic : IntegrableOn (fun y => w₀ * primeLogDensity φ χ β y) (Set.Ioc s t) :=
    (continuousOn_const.mul hc).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have heq : (∫ y in Set.Ioc s t, w y * primeLogDensity φ χ β y) -
      w₀ * (∫ y in Set.Ioc s t, primeLogDensity φ χ β y) =
      ∫ y in Set.Ioc s t, (w y - w₀) * primeLogDensity φ χ β y := by
    rw [← integral_const_mul, ← integral_sub hiw hic]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y _
    ring
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := 2 * η)
    (f := fun y => (w y - w₀) * primeLogDensity φ χ β y)
    (fun y hy => by
      have hy' := (Set.uIoc_of_le hst) ▸ hy
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_mul (hw y hy')
        (primeLogDensity_abs_le_two φ χ β hφ hχ hβ (hs.trans hy'.1.le))
        (abs_nonneg _) hη).trans_eq (mul_comm η 2))
  rw [intervalIntegral.integral_of_le hst, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at h
  exact h.trans (by nlinarith)

/-- Transfer a bare progression estimate to the actual cutoff-weighted
prime cell. The cutoff variation is controlled independently of its sign. -/
theorem weighted_prime_log_interval_error (q a : ℕ) (φ χ β : ℝ)
    (hφ : 1 ≤ φ) (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {s t : ℝ}
    (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1)
    (w : ℝ → ℝ) (hwc : ContinuousOn w (Set.Icc s t)) (w₀ η δ : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc s t, |w y - w₀| ≤ η)
    (hbare : |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity φ χ β y| ≤ δ) :
    |weightedReciprocalPrimeInterval q a s t w -
      ∫ y in Set.Ioc s t, w y * primeLogDensity φ χ β y| ≤
      (|w₀| + η) * δ + 4 * η := by
  let S := reciprocalPrimeInterval q a (Real.exp s) (Real.exp t)
  let I := ∫ y in Set.Ioc s t, primeLogDensity φ χ β y
  let W := weightedReciprocalPrimeInterval q a s t w
  let J := ∫ y in Set.Ioc s t, w y * primeLogDensity φ χ β y
  have hS : S ≤ δ + 2 := by
    have hI := primeLogDensity_integral_abs_le_two φ χ β hφ hχ hβ hs hst hshort
    have hbare' := (le_abs_self _).trans hbare
    have hI' := (le_abs_self _).trans hI
    dsimp [S, I] at *
    linarith
  have hfreeze := weightedReciprocalPrimeInterval_freeze q a s t w w₀ η hw
  have hweighted := primeLogDensity_integral_freeze φ χ β hφ hχ hβ
    hs hst hshort w hwc w₀ η hη hw
  have hscale : |w₀ * S - w₀ * I| ≤ |w₀| * δ := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hbare (abs_nonneg _)
  have h₁ := norm_sub_le_norm_sub_add_norm_sub W (w₀ * S) (w₀ * I)
  have h₂ := norm_sub_le_norm_sub_add_norm_sub W (w₀ * I) J
  simp only [Real.norm_eq_abs] at h₁ h₂
  have hweighted' : |w₀ * I - J| ≤ 2 * η := by
    rw [abs_sub_comm]
    exact hweighted
  have hηS : η * S ≤ η * (δ + 2) := mul_le_mul_of_nonneg_left hS hη
  dsimp [S, I, W, J] at *
  nlinarith

end Ostmann

end OAI

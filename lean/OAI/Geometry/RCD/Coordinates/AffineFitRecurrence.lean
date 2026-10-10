import OAI.Geometry.RCD.Harmonic.PinchingEnvelope

namespace OAI

/-! # The squared affine-fit recurrence and its geometric envelope -/

open scoped BigOperators

namespace RegularPointCoordinates

/-- Squaring a single affine-improvement estimate costs a fixed factor,
and preserves the Poisson defect without taking its square root. -/
theorem affine_fit_squared_step {e e' a C P : ℝ}
    (he : 0 ≤ e) (he' : 0 ≤ e') (ha : 0 ≤ a) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hfit : e' ≤ a * e + C * Real.sqrt P) :
    e' ^ 2 ≤ 2 * a ^ 2 * e ^ 2 + 2 * C ^ 2 * P := by
  have hsq := (sq_le_sq₀ he' (by positivity : 0 ≤ a * e + C * Real.sqrt P)).mpr hfit
  have hroot := Real.sq_sqrt hP
  have hyoung := sq_nonneg (a * e - C * Real.sqrt P)
  nlinarith

theorem forwardDefect_succ (σ η : ℝ) (P : ℕ → ℝ) (i : ℕ) :
    forwardDefect σ η P (i + 1) = σ * forwardDefect σ η P i + P (i + 1) := by
  have he : (∑ j ∈ Finset.range (i + 1), σ ^ (i + 1 - j) * P j) =
      σ * ∑ j ∈ Finset.range (i + 1), σ ^ (i - j) * P j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hnat : i + 1 - j = (i - j) + 1 := by omega
    rw [hnat, pow_succ]
    ring
  simp only [forwardDefect, Finset.sum_range_succ,
    Nat.sub_self, pow_zero, one_mul, he, pow_succ]
  ring

theorem forwardDefect_propagates {σ η : ℝ} (hσ : 0 ≤ σ)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (i k : ℕ) :
    σ ^ k * forwardDefect σ η P i ≤ forwardDefect σ η P (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := mul_le_mul_of_nonneg_left ih hσ
    rw [show i + (k + 1) = (i + k) + 1 by omega, forwardDefect_succ, pow_succ]
    nlinarith [hP (i + k + 1)]

/-- A stride of `m` leaves the final new source term available, even
though all intermediate source terms are discarded from the bound. -/
theorem forwardDefect_stride {σ η : ℝ} (hσ : 0 ≤ σ)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) {m : ℕ} (hm : 0 < m) (i : ℕ) :
    σ ^ m * forwardDefect σ η P i + P (i + m) ≤
      forwardDefect σ η P (i + m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hh := mul_le_mul_of_nonneg_left (forwardDefect_propagates (η := η) hσ hP i k) hσ
  rw [show i + (k + 1) = (i + k) + 1 by omega, forwardDefect_succ, pow_succ]
  nlinarith

/-- The same comparison works simultaneously in all residue classes of
the affine-improvement stride. This is the discrete step used before
the two-sided smoothing in radial pinching. -/
theorem affine_fit_le_forwardDefect {σ η : ℝ} (hσ : 0 ≤ σ)
    {P F : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) {m : ℕ} (hm : 0 < m)
    (hinitial : ∀ i < m, F i ≤ η * σ ^ i)
    (hstep : ∀ i, F (i + m) ≤ σ ^ m * F i + P (i + m)) :
    ∀ i, F i ≤ forwardDefect σ η P i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hi : i < m
    · exact (hinitial i hi).trans (le_add_of_nonneg_right
        (Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hσ _) (hP j)))
    · have hj : i - m < i := by omega
      have he : i - m + m = i := by omega
      have h := (hstep (i - m)).trans
        (add_le_add (mul_le_mul_of_nonneg_left (ih (i - m) hj) (pow_nonneg hσ m)) le_rfl)
      have hg := forwardDefect_stride (η := η) hσ hP hm (i - m)
      rw [he] at h hg
      exact h.trans hg

end RegularPointCoordinates

end OAI

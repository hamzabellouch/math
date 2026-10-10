import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Problem337.ThreePrimeContinuousFourier

/-- Positive-sign integral Fourier phase on the unit interval. -/
def phase (n : ℤ) (x : ℝ) : ℂ := fourier n (x : AddCircle (1 : ℝ))

lemma phase_exp (n : ℤ) (x : ℝ) :
    phase n x = Complex.exp (2 * Real.pi * Complex.I * n * x) := by
  simp [phase]

lemma phase_continuous (n : ℤ) : Continuous (phase n) := by
  unfold phase
  fun_prop

lemma phase_add (m n : ℤ) (x : ℝ) :
    phase (m + n) x = phase m x * phase n x := fourier_add

@[simp] lemma phase_zero (x : ℝ) : phase 0 x = 1 := fourier_zero

@[simp] lemma norm_phase (n : ℤ) (x : ℝ) : ‖phase n x‖ = 1 :=
  Circle.norm_coe _

lemma phase_neg (n : ℤ) (x : ℝ) :
    phase (-n) x = starRingEnd ℂ (phase n x) := fourier_neg

lemma phase_sub (m n : ℤ) (x : ℝ) :
    phase (m - n) x = phase m x * starRingEnd ℂ (phase n x) := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

/-- Exact integer-frequency orthogonality, with no limiting argument. -/
theorem integral_phase (n : ℤ) :
    (∫ x in (0 : ℝ)..1, phase n x) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  rw [fourierCoeff_eq_intervalIntegral _ _ (0 : ℝ)] at h
  simpa [phase, Pi.single_apply, eq_comm] using h

lemma phase_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) (x : ℝ) :
    phase (∑ i ∈ s, f i) x = ∏ i ∈ s, phase (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, phase_add, ih]

/-- Exact extraction of every weighted coefficient of a finite Fourier power.
The formula also covers the empty indexing type and the zeroth power. -/
theorem weighted_power_integral {ι : Type*} [Fintype ι]
    (f : ι → ℤ) (w : ι → ℂ) (k : ℕ) (u : ℤ) :
    (∫ x in (0 : ℝ)..1,
      (∑ a : ι, w a * phase (f a) x) ^ k * phase (-u) x) =
    ∑ v : Fin k → ι, if (∑ i, f (v i)) = u then ∏ i, w (v i) else 0 := by
  classical
  have hexpand (x : ℝ) :
      (∑ a : ι, w a * phase (f a) x) ^ k * phase (-u) x =
      ∑ v : Fin k → ι, (∏ i, w (v i)) * phase ((∑ i, f (v i)) - u) x := by
    rw [Fintype.sum_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.prod_mul_distrib, ← phase_sum, mul_assoc, ← phase_add]
    rfl
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [intervalIntegral.integral_const_mul, integral_phase]
    by_cases h : (∑ i, f (v i)) = u
    · simp [h]
    · simp [sub_eq_zero, h]
  · intro v hv
    exact (continuous_const.mul (phase_continuous _)).intervalIntegrable _ _

private def tripleEquiv (ι : Type*) : (Fin 3 → ι) ≃ ι × ι × ι where
  toFun v := (v 0, v 1, v 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv t := by rcases t with ⟨a, b, c⟩; rfl

/-- The continuous cubic identity in nested-sum form. Frequencies need not
be injective, and arbitrary complex weights are allowed. -/
theorem weighted_triple_integral {ι : Type*} [Fintype ι]
    (f : ι → ℤ) (w : ι → ℂ) (u : ℤ) :
    (∫ x in (0 : ℝ)..1,
      (∑ a : ι, w a * phase (f a) x) ^ 3 * phase (-u) x) =
    ∑ a : ι, ∑ b : ι, ∑ c : ι,
      if f a + f b + f c = u then w a * w b * w c else 0 := by
  classical
  rw [weighted_power_integral]
  calc
    _ = ∑ t : ι × ι × ι,
        if f t.1 + f t.2.1 + f t.2.2 = u then w t.1 * w t.2.1 * w t.2.2 else 0 := by
      apply Fintype.sum_equiv (tripleEquiv ι)
      intro v
      simp [tripleEquiv, Fin.sum_univ_three, Fin.prod_univ_three]
      rfl
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- Finite-set version of exact continuous cubic coefficient extraction. -/
theorem weighted_triple_finset_integral {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) (w : ι → ℂ) (u : ℤ) :
    (∫ x in (0 : ℝ)..1,
      (∑ a ∈ s, w a * phase (f a) x) ^ 3 * phase (-u) x) =
    ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
      if f a + f b + f c = u then w a * w b * w c else 0 := by
  classical
  have h := weighted_triple_integral (fun a : s => f a) (fun a : s => w a) u
  have hs (x : ℝ) : (∑ a : s, w a * phase (f a) x) =
      ∑ a ∈ s, w a * phase (f a) x :=
    Finset.sum_coe_sort s (fun a => w a * phase (f a) x)
  simp_rw [hs] at h
  rw [Finset.sum_coe_sort s (fun a => ∑ b : s, ∑ c : s,
    if f a + f b + f c = u then w a * w b * w c else 0)] at h
  have hs2 (a : ι) : (∑ b : s, ∑ c : s,
      if f a + f b + f c = u then w a * w b * w c else 0) =
      ∑ b ∈ s, ∑ c : s,
      if f a + f b + f c = u then w a * w b * w c else 0 :=
    Finset.sum_coe_sort s (fun b => ∑ c : s,
      if f a + f b + f c = u then w a * w b * w c else 0)
  simp_rw [hs2] at h
  have hs3 (a b : ι) : (∑ c : s,
      if f a + f b + f c = u then w a * w b * w c else 0) =
      ∑ c ∈ s, if f a + f b + f c = u then w a * w b * w c else 0 :=
    Finset.sum_coe_sort s (fun c =>
      if f a + f b + f c = u then w a * w b * w c else 0)
  simp_rw [hs3] at h
  exact h

end Problem337.ThreePrimeContinuousFourier

end

end OAI

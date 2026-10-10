import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Problem337.ThreePrimeContinuousEnergy

abbrev UnitCircle := AddCircle (1 : ℝ)

/-- A finite exponential polynomial on the normalized unit circle. -/
def polynomial (s : Finset ℤ) (w : ℤ → ℂ) (x : UnitCircle) : ℂ :=
  ∑ n ∈ s, w n * fourier n x

lemma continuous_polynomial (s : Finset ℤ) (w : ℤ → ℂ) :
    Continuous (polynomial s w) := by
  unfold polynomial
  fun_prop

lemma integrable_of_continuous {E : Type*} [NormedAddCommGroup E]
    (f : UnitCircle → E) (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Character orthogonality with the orientation used in a squared norm. -/
theorem integral_fourier_mul_conj (m n : ℤ) :
    (∫ x : UnitCircle, fourier m x * conj (fourier n x)
      ∂AddCircle.haarAddCircle) = if m = n then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) m) n
  simpa only [fourierCoeff, smul_eq_mul, fourier_neg, Pi.single_apply,
    mul_comm, eq_comm] using h

/-- Exact continuous Parseval for finitely supported Fourier coefficients. -/
theorem polynomial_parseval (s : Finset ℤ) (w : ℤ → ℂ) :
    (∫ x : UnitCircle, ‖polynomial s w x‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ n ∈ s, ‖w n‖ ^ 2 := by
  classical
  have hexpand (x : UnitCircle) :
      polynomial s w x * conj (polynomial s w x) =
        ∑ m ∈ s, ∑ n ∈ s,
          (w m * conj (w n)) * (fourier m x * conj (fourier n x)) := by
    simp only [polynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hint : (∫ x : UnitCircle, polynomial s w x * conj (polynomial s w x)
      ∂AddCircle.haarAddCircle) = ∑ n ∈ s, w n * conj (w n) := by
    simp_rw [hexpand]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul, integral_fourier_mul_conj]
        simp [hm]
      · intro n hn
        apply integrable_of_continuous
        fun_prop
    · intro m hm
      apply integrable_of_continuous
      fun_prop
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hint
  rw [integral_complex_ofReal] at hint
  exact_mod_cast hint

/-- A measure-theoretic cubic minor-set bound. Only the square energy must
be integrable; the actual supremum and phase estimates are explicit. -/
theorem cubic_setIntegral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f phase : α → ℂ) (minor : Set α)
    (hmeas : MeasurableSet minor) (B : ℝ) (hB : 0 ≤ B)
    (henergy : Integrable (fun x => ‖f x‖ ^ 2) μ)
    (hminor : ∀ x ∈ minor, ‖f x‖ ≤ B)
    (hphase : ∀ x ∈ minor, ‖phase x‖ ≤ 1) :
    ‖∫ x in minor, f x ^ 3 * phase x ∂μ‖ ≤
      B * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hpoint : ∀ᵐ x ∂μ.restrict minor,
      ‖f x ^ 3 * phase x‖ ≤ B * ‖f x‖ ^ 2 := by
    filter_upwards [ae_restrict_mem hmeas] with x hx
    rw [norm_mul, norm_pow]
    calc
      ‖f x‖ ^ 3 * ‖phase x‖ ≤ ‖f x‖ ^ 3 := by
        simpa using mul_le_mul_of_nonneg_left (hphase x hx)
          (pow_nonneg (norm_nonneg _) 3)
      _ ≤ B * ‖f x‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right (hminor x hx) (sq_nonneg ‖f x‖)]
  calc
    _ ≤ ∫ x in minor, B * ‖f x‖ ^ 2 ∂μ :=
      norm_integral_le_of_norm_le ((henergy.const_mul B).restrict) hpoint
    _ = B * ∫ x in minor, ‖f x‖ ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ B * ∫ x, ‖f x‖ ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral henergy (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))) hB

/-- Continuous minor-frequency control for finite exponential polynomials,
with exact coefficient energy and normalized Haar measure. -/
theorem polynomial_minor_cubic_bound (s : Finset ℤ) (w : ℤ → ℂ)
    (phase : UnitCircle → ℂ) (minor : Set UnitCircle)
    (hmeas : MeasurableSet minor) (B : ℝ) (hB : 0 ≤ B)
    (hminor : ∀ x ∈ minor, ‖polynomial s w x‖ ≤ B)
    (hphase : ∀ x ∈ minor, ‖phase x‖ ≤ 1) :
    ‖∫ x in minor, polynomial s w x ^ 3 * phase x ∂AddCircle.haarAddCircle‖ ≤
      B * ∑ n ∈ s, ‖w n‖ ^ 2 := by
  have henergy : Integrable (fun x => ‖polynomial s w x‖ ^ 2)
      AddCircle.haarAddCircle := by
    apply integrable_of_continuous
    exact (continuous_polynomial s w).norm.pow 2
  simpa only [polynomial_parseval] using
    cubic_setIntegral_bound AddCircle.haarAddCircle (polynomial s w) phase minor
      hmeas B hB henergy hminor hphase

/-- The circle polynomial evaluated on a real argument is the usual
positive-sign exponential sum. -/
lemma polynomial_coe_real (s : Finset ℤ) (w : ℤ → ℂ) (x : ℝ) :
    polynomial s w (x : UnitCircle) =
      ∑ n ∈ s, w n * Complex.exp (2 * Real.pi * Complex.I * n * x) := by
  simp only [polynomial, fourier_coe_apply, Complex.ofReal_one, div_one]

/-- Parseval on the usual unit interval, with Lebesgue measure. -/
theorem polynomial_parseval_interval (s : Finset ℤ) (w : ℤ → ℂ) :
    (∫ x : ℝ in 0..1, ‖polynomial s w (x : UnitCircle)‖ ^ 2) =
      ∑ n ∈ s, ‖w n‖ ^ 2 := by
  have h := AddCircle.intervalIntegral_preimage (1 : ℝ) 0
    (fun x : UnitCircle => ‖polynomial s w x‖ ^ 2)
  have heq : (∫ x : ℝ in 0..1, ‖polynomial s w (x : UnitCircle)‖ ^ 2) =
      ∫ x : UnitCircle, ‖polynomial s w x‖ ^ 2 ∂AddCircle.haarAddCircle := by
    simpa only [zero_add, AddCircle.volume_eq_smul_haarAddCircle,
      ENNReal.ofReal_one, one_smul] using h
  exact heq.trans (polynomial_parseval s w)

/-- The classical continuous minor-arc norm bound. The minor set can be any
measurable subset of `[0,1]`; the phase is arbitrary of modulus at most one. -/
theorem polynomial_interval_minor_cubic_bound (s : Finset ℤ) (w : ℤ → ℂ)
    (phase : ℝ → ℂ) (minor : Set ℝ) (hmeas : MeasurableSet minor)
    (hsubset : minor ⊆ Set.Icc 0 1) (B : ℝ) (hB : 0 ≤ B)
    (hminor : ∀ x ∈ minor, ‖polynomial s w (x : UnitCircle)‖ ≤ B)
    (hphase : ∀ x ∈ minor, ‖phase x‖ ≤ 1) :
    ‖∫ x in minor, polynomial s w (x : UnitCircle) ^ 3 * phase x‖ ≤
      B * ∑ n ∈ s, ‖w n‖ ^ 2 := by
  have hcont : Continuous (fun x : ℝ => ‖polynomial s w (x : UnitCircle)‖ ^ 2) := by
    simp only [polynomial_coe_real]
    fun_prop
  have henergy := hcont.integrableOn_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)
  have h := cubic_setIntegral_bound (volume.restrict (Set.Icc 0 1))
    (fun x : ℝ => polynomial s w (x : UnitCircle)) phase minor hmeas B hB
    henergy hminor hphase
  rw [Measure.restrict_restrict_of_subset hsubset] at h
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    polynomial_parseval_interval] at h
  exact h

/-- A naturally indexed exponential sum, in the ordinary real phase variable. -/
def natPolynomial (s : Finset ℕ) (w : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ s, w n * Complex.exp (2 * Real.pi * Complex.I * n * x)

lemma polynomial_nat_image (s : Finset ℕ) (w : ℕ → ℂ) (x : ℝ) :
    polynomial (s.image (fun n : ℕ => (n : ℤ))) (fun n => w n.toNat)
      (x : UnitCircle) = natPolynomial s w x := by
  classical
  rw [polynomial_coe_real, Finset.sum_image]
  · simp only [Int.toNat_natCast, Int.cast_natCast, natPolynomial]
  · intro a ha b hb hab
    exact Int.ofNat.inj hab

lemma nat_image_energy (s : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ s.image (fun n : ℕ => (n : ℤ)), ‖w n.toNat‖ ^ 2) =
      ∑ n ∈ s, ‖w n‖ ^ 2 := by
  classical
  rw [Finset.sum_image]
  · simp only [Int.toNat_natCast]
  · intro a ha b hb hab
    exact Int.ofNat.inj hab

/-- Exact unit-interval energy for arbitrary naturally indexed finite sums. -/
theorem nat_polynomial_parseval_interval (s : Finset ℕ) (w : ℕ → ℂ) :
    (∫ x : ℝ in 0..1, ‖natPolynomial s w x‖ ^ 2) = ∑ n ∈ s, ‖w n‖ ^ 2 := by
  simpa only [polynomial_nat_image, nat_image_energy] using
    polynomial_parseval_interval (s.image (fun n : ℕ => (n : ℤ))) (fun n => w n.toNat)

/-- The continuous cubic minor-arc estimate in natural-frequency notation. -/
theorem nat_polynomial_interval_minor_cubic_bound (s : Finset ℕ) (w : ℕ → ℂ)
    (phase : ℝ → ℂ) (minor : Set ℝ) (hmeas : MeasurableSet minor)
    (hsubset : minor ⊆ Set.Icc 0 1) (B : ℝ) (hB : 0 ≤ B)
    (hminor : ∀ x ∈ minor, ‖natPolynomial s w x‖ ≤ B)
    (hphase : ∀ x ∈ minor, ‖phase x‖ ≤ 1) :
    ‖∫ x in minor, natPolynomial s w x ^ 3 * phase x‖ ≤
      B * ∑ n ∈ s, ‖w n‖ ^ 2 := by
  have h := polynomial_interval_minor_cubic_bound
    (s.image (fun n : ℕ => (n : ℤ))) (fun n => w n.toNat) phase minor
    hmeas hsubset B hB
    (by simpa only [polynomial_nat_image] using hminor) hphase
  simpa only [polynomial_nat_image, nat_image_energy] using h

end Problem337.ThreePrimeContinuousEnergy

end

end OAI

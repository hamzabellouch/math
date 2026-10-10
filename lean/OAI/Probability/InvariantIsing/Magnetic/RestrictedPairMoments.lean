import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairSpinKernel

namespace OAI

/-! Conditional coordinate means in the constrained block and their
actual two-spin interpretation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def restrictedCoordinateMean {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i)
    (j : Fin N) (z : Fin N → ℝ) : ℝ :=
  ∫ σ, spinValue (σ j) ∂restrictedTailSpinKernel hN S hS n b v hb z

def restrictedPairCoordinateMean {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ j < n, 0 < b j)
    (i : Fin (n + 1)) (j : Fin N) (z : Fin N → ℝ) : ℝ :=
  ∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j) ∂restrictedPairSpinKernel hN S hS n b v hb i z

lemma measurable_restrictedCoordinateMean {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (j : Fin N) :
    Measurable (restrictedCoordinateMean hN S hS n b v hb j) := by
  have hm : Measurable (fun p : (Fin N → ℝ) × Spin N => spinValue (p.2 j)) :=
    (measurable_of_finite (fun σ : Spin N => spinValue (σ j))).comp measurable_snd
  exact (hm.stronglyMeasurable.integral_kernel_prod_right'
    (κ := restrictedTailSpinKernel hN S hS n b v hb)).measurable

lemma measurable_restrictedPairCoordinateMean {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) (j : Fin N) :
    Measurable (restrictedPairCoordinateMean hN S hS n b v hb i j) := by
  have hm : Measurable (fun p : (Fin N → ℝ) × (Spin N × Spin N) =>
      spinValue (p.2.1 j) * spinValue (p.2.2 j)) :=
    (measurable_of_finite (fun σ : Spin N × Spin N => spinValue (σ.1 j) * spinValue (σ.2 j))).comp measurable_snd
  exact (hm.stronglyMeasurable.integral_kernel_prod_right'
    (κ := restrictedPairSpinKernel hN S hS n b v hb i)).measurable

lemma restrictedCoordinateMean_bound {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (j : Fin N) (z : Fin N → ℝ) :
    |restrictedCoordinateMean hN S hS n b v hb j z| ≤ 1 := by
  have he := norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (μ := restrictedTailSpinKernel hN S hS n b v hb z)
    (f := fun σ => spinValue (σ j)) (Filter.Eventually.of_forall (fun σ => by
      simp only [Real.norm_eq_abs, abs_spinValue, le_refl]))
  simpa only [restrictedCoordinateMean, Real.norm_eq_abs, measureReal_def,
    measure_univ, ENNReal.toReal_one, mul_one] using he

lemma restrictedPairCoordinateMean_bound {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) (j : Fin N) (z : Fin N → ℝ) :
    |restrictedPairCoordinateMean hN S hS n b v hb i j z| ≤ 1 := by
  have he := norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (μ := restrictedPairSpinKernel hN S hS n b v hb i z)
    (f := fun σ => spinValue (σ.1 j) * spinValue (σ.2 j))
    (Filter.Eventually.of_forall (fun σ => by simp only [Real.norm_eq_abs, abs_mul, abs_spinValue, mul_one, le_refl]))
  simpa only [restrictedPairCoordinateMean, Real.norm_eq_abs, measureReal_def,
    measure_univ, ENNReal.toReal_one, mul_one] using he

lemma restrictedPairSpinKernel_zero {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) :
    restrictedPairSpinKernel hN S hS n b v hb 0 =
      restrictedTailSpinKernel hN S hS n b v hb ×ₖ restrictedTailSpinKernel hN S hS n b v hb := by
  cases n <;> rfl

lemma restrictedPairCoordinateMean_zero {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (j : Fin N) (z : Fin N → ℝ) :
    restrictedPairCoordinateMean hN S hS n b v hb 0 j z =
      (restrictedCoordinateMean hN S hS n b v hb j z) ^ 2 := by
  rw [restrictedPairCoordinateMean, restrictedPairSpinKernel_zero, Kernel.prod_apply,
    integral_prod_mul (fun σ : Spin N => spinValue (σ j)) (fun σ : Spin N => spinValue (σ j))]
  rw [pow_two]
  rfl

end InvariantIsing

end

end OAI

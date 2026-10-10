import OAI.Probability.InvariantIsing.Arrays.TensorFieldDerivativeMean
import OAI.Probability.IsingPerceptron.OrderedQuantile

namespace OAI

/-! Field continuity for the actual complete tensor perturbation, including
zero increments. The bound is uniform in all other finite parameters. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

theorem tensorNamespacedMeanPressure_field_cost {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    |tensorNamespacedMeanPressure μ eig c I degree amp n b r (fun i => h i + g i) -
      tensorNamespacedMeanPressure μ eig c I degree amp n b r h| ≤ g n / 2 := by
  have he := tensorNamespacedMeanPressure_field_insert μ eig c I degree amp n b r
    h g hh h0 hg g0 1 zero_le_one
  simp only [one_mul] at he
  have hc := random_cylinder_cgf_mean_bounds
    (P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
    (measurable_tensorNamespacedReference eig c I degree amp n r h)
    (tensorLinearCoefficients n g)
    (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le) 1
  simp only [one_pow, one_mul] at hc
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc' : tensorFieldCGFMean μ eig c I degree amp n b r h g 1 / N ≤ g n / 2 := by
    rw [div_le_iff₀ hn]
    unfold tensorFieldCGFMean
    simp only [Real.sqrt_one]
    nlinarith [hc.2]
  have hc0 : 0 ≤ tensorFieldCGFMean μ eig c I degree amp n b r h g 1 / N := by
    apply div_nonneg _ hn.le
    simpa only [tensorFieldCGFMean, Real.sqrt_one] using hc.1
  rw [he]
  unfold tensorFieldInsertionMean
  simp only [one_mul]
  apply abs_le.mpr
  constructor <;> linarith

theorem tensorNamespacedMeanPressure_field_modulus {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (a c' : Fin (n + 1) → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hc : ∀ j, 0 ≤ c' j) :
    |tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath a) -
      tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath c')| ≤
      (∑ j, |a j - c' j|) / 2 := by
  let d : Fin (n + 1) → ℝ := fun j => min (a j) (c' j)
  have hd : ∀ j, 0 ≤ d j := fun j => le_min (ha j) (hc j)
  have had : ∀ j, 0 ≤ a j - d j := fun j => sub_nonneg.mpr (min_le_left _ _)
  have hcd : ∀ j, 0 ≤ c' j - d j := fun j => sub_nonneg.mpr (min_le_right _ _)
  have heA := tensorNamespacedMeanPressure_field_cost hN μ eig c I degree amp n b r
    (finiteFieldPath d) (finiteFieldPath (fun j => a j - d j))
    (monotone_finiteFieldPath hd) (finiteFieldPath_nonneg hd 0)
    (monotone_finiteFieldPath had) (finiteFieldPath_nonneg had 0)
  have heC := tensorNamespacedMeanPressure_field_cost hN μ eig c I degree amp n b r
    (finiteFieldPath d) (finiteFieldPath (fun j => c' j - d j))
    (monotone_finiteFieldPath hd) (finiteFieldPath_nonneg hd 0)
    (monotone_finiteFieldPath hcd) (finiteFieldPath_nonneg hcd 0)
  simp only [finiteFieldPath_sub, add_sub_cancel] at heA heC
  have hs : finiteFieldPath a n - finiteFieldPath d n +
      (finiteFieldPath c' n - finiteFieldPath d n) = ∑ j, |a j - c' j| := by
    simp only [finiteFieldPath_last, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [d]
    rcases le_total (a j) (c' j) with hle | hle
    · rw [min_eq_left hle, abs_of_nonpos (sub_nonpos.mpr hle)]; ring
    · rw [min_eq_right hle, abs_of_nonneg (sub_nonneg.mpr hle)]; ring
  have ht := abs_sub_le
    (tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath a))
    (tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath d))
    (tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath c'))
  rw [abs_sub_comm (tensorNamespacedMeanPressure μ eig c I degree amp n b r (finiteFieldPath d))] at ht
  linarith

end InvariantIsing

end

end OAI

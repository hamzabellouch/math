import OAI.Probability.InvariantIsing.Arrays.TensorTemperatureDerivative
import OAI.Probability.InvariantIsing.Arrays.FullPerturbationMinima

namespace OAI

/-! Uniform temperature continuity of the enriched pressure and its
identity with the pressure under the original disorder law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma tensorNamespacedMeanPressure_eq_disorder {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hb : CascadeExponents n b) :
    tensorNamespacedMeanPressure μ eig c I degree amp n b r h =
      (∫ p, tensorDisorderPressure eig c I degree amp n p
        ∂μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1))
          (tensorPathProfile I degree n r h 0))) - h n / 2 := by
  have hlaw := tensorNamespacedPressure_law μ eig c I degree amp n b r h hb
  unfold tensorNamespacedMeanPressure
  exact congrArg (fun x => x - h n / 2) (hlaw.integral_eq.trans
    (integral_map (measurable_tensorDisorderPressure eig c I degree amp n).aemeasurable
      aestronglyMeasurable_id))

lemma tensorNamespacedMeanPressure_eq_perturbation {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) (hb : CascadeExponents n b) :
    tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
      (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
      n b (fun j => enumeratedTreeDegree m j) h =
      tensorPerturbationPressureMean μ eig c I u v t n b h - h n / 2 :=
  tensorNamespacedMeanPressure_eq_disorder μ _ c I _ _ n b _ h hb

lemma abs_tensorNamespaced_interactionEnergy_le {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig modelEig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) :
    |tensorNamespacedObservableAverage μ modelEig c I degree amp n b r h
      (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1)| ≤ K / 2 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hb (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf n) :
      |(N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1| ≤ K / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
    calc
      _ ≤ (N : ℝ)⁻¹ * (K * N / 2) := mul_le_mul_of_nonneg_left
        (abs_rotatedEnergy_le eig (specialRotation U) K hK x.1) (by positivity)
      _ = K / 2 := by field_simp
  have hi (p : TensorFlatDisorder N n) :
      ‖∫ x, (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation p.1.1) x.1
        ∂tensorNamespacedReference modelEig c I degree amp n r h p‖ ≤ K / 2 := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := tensorNamespacedReference modelEig c I degree amp n r h p)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb p.1.1 x)
  unfold tensorNamespacedObservableAverage
  simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const
      (μ := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
      (ae_of_all _ hi)

theorem tensorNamespacedMeanPressure_temperature_modulus {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (s t : ℝ) :
    |tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v s) c I degree amp n b r h -
      tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I degree amp n b r h| ≤
      (K / 2) * |s - t| := by
  have hd (a : ℝ) (_ : a ∈ (univ : Set ℝ)) :=
    (hasDerivAt_tensorNamespacedMeanPressure_temperature hN μ eig c I v degree amp n b r h hh h0 K hK a).hasDerivWithinAt
      (s := univ)
  have hb (a : ℝ) (_ : a ∈ (univ : Set ℝ)) :
      ‖tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I v a)
        c I degree amp n b r h
        (fun U x => (N : ℝ)⁻¹ * rotatedEnergy eig (specialRotation U) x.1)‖ ≤ K / 2 := by
    rw [Real.norm_eq_abs]
    exact abs_tensorNamespaced_interactionEnergy_le hN μ eig _ c I degree amp n b r h K hK
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hd hb (mem_univ t) (mem_univ s)

end InvariantIsing

end

end OAI

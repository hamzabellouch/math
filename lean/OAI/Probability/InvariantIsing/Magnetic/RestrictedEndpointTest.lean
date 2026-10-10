import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldPublishedInput
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairRecursion
import OAI.Probability.InvariantIsing.Fields.FieldPublishedEvaluation

namespace OAI

/-! Coordinate spin tests of the constrained endpoint law. These are
consequences of the published marking input and the actual spin kernels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def restrictedTerminalPairMean {N : ℕ} (S : Finset (Spin N)) (j : Fin N)
    (y : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  ∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j)
    ∂(restrictedSpinKernel S ∥ₖ restrictedSpinKernel S) y

lemma measurable_restrictedTerminalPairMean {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (j : Fin N) : Measurable (restrictedTerminalPairMean S j) := by
  let _ := restrictedSpinKernel_markov S hS
  have hm : Measurable (fun p : ((Fin N → ℝ) × (Fin N → ℝ)) × (Spin N × Spin N) =>
      spinValue (p.2.1 j) * spinValue (p.2.2 j)) :=
    (measurable_of_finite (fun σ : Spin N × Spin N => spinValue (σ.1 j) * spinValue (σ.2 j))).comp measurable_snd
  exact (hm.stronglyMeasurable.integral_kernel_prod_right'
    (κ := restrictedSpinKernel S ∥ₖ restrictedSpinKernel S)).measurable

lemma restrictedTerminalPairMean_bound {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (j : Fin N) (y : (Fin N → ℝ) × (Fin N → ℝ)) : |restrictedTerminalPairMean S j y| ≤ 1 := by
  let _ := restrictedSpinKernel_markov S hS
  have he := norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (μ := (restrictedSpinKernel S ∥ₖ restrictedSpinKernel S) y)
    (f := fun σ => spinValue (σ.1 j) * spinValue (σ.2 j))
    (Filter.Eventually.of_forall (fun σ => by
      simp only [Real.norm_eq_abs, abs_mul, abs_spinValue, mul_one, le_refl]))
  simpa only [restrictedTerminalPairMean, Real.norm_eq_abs, measureReal_def,
    measure_univ, ENNReal.toReal_one, mul_one] using he

lemma restrictedPairCoordinateMean_endpoint {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (i : Fin (n + 1)) (j : Fin N) (z : Fin N → ℝ) :
    restrictedPairCoordinateMean hN S hS n b v hb i j z =
      ∫ y, restrictedTerminalPairMean S j y ∂restrictedPairEndpointKernel hN S hS n b v hb i z := by
  let _ := restrictedSpinKernel_markov S hS
  rw [restrictedPairCoordinateMean, restrictedPairSpinKernel_endpoint,
    Kernel.integral_comp (Integrable.of_finite)]
  rfl

def restrictedEndpointCoordinateTest {N : ℕ} (S : Finset (Spin N)) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    (p : ℕ × ((Fin N → ℝ) × (Fin N → ℝ))) : ℝ :=
  Φ (q (fieldDepthLevel h p.1)) * restrictedTerminalPairMean S j p.2

lemma measurable_restrictedEndpointCoordinateTest {N : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) :
    Measurable (restrictedEndpointCoordinateTest S h q Φ j) :=
  ((measurable_of_countable (fun d => Φ (q (fieldDepthLevel h d)))).comp measurable_fst).mul
    ((measurable_restrictedTerminalPairMean S hS j).comp measurable_snd)

lemma restrictedEndpointCoordinateTest_bound {N : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C)
    (p : ℕ × ((Fin N → ℝ) × (Fin N → ℝ))) :
    |restrictedEndpointCoordinateTest S h q Φ j p| ≤ C := by
  rw [restrictedEndpointCoordinateTest, abs_mul]
  exact (mul_le_mul_of_nonneg_left (restrictedTerminalPairMean_bound S hS j p.2)
    (abs_nonneg _)).trans (by simpa only [mul_one] using hΦ _)

theorem restricted_field_published_coordinate_test
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) (z : Fin N → ℝ) :
    restrictedFieldTiltedPairMean S h z (restrictedEndpointCoordinateTest S h q Φ j) =
      ∫ α : ℕ → LabeledLeaf h.depth,
        Φ (q (fieldCommonLevel h α)) * restrictedPairCoordinateMean hN S hS h.depth
          (chainExponent h.cut) (fieldStepVariance h)
          (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1)
          (fieldCommonLevel h α) j z
        ∂cascadeReplicaLaw h.depth (chainExponent h.cut) := by
  rw [hpub N hN S hS h z _ (measurable_restrictedEndpointCoordinateTest S hS h q Φ j)
    ⟨C, restrictedEndpointCoordinateTest_bound S hS h q Φ j hΦ⟩]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun α => by
    have hc : fieldDepthLevel h (fieldCommonLevel h α).val = fieldCommonLevel h α := by
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt_succ (fieldCommonLevel h α).isLt)
    simp only [restrictedEndpointCoordinateTest, hc, integral_const_mul,
      restrictedPairCoordinateMean_endpoint])

end InvariantIsing

end

end OAI

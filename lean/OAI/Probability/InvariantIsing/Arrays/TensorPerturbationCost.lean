import OAI.Probability.InvariantIsing.Arrays.TensorGaussianMean
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFlatMean
import OAI.Probability.InvariantIsing.Arrays.TensorProfiles
import OAI.Probability.InvariantIsing.Arrays.PerturbationWeights

namespace OAI

/-! Removing the actual Gaussian monomial perturbation has vanishing pressure cost. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorLeafCoefficients_mixed_cross {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (a b : Fin k → ℝ) (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLeafCoefficients U I degree a n v x)
      (tensorLeafCoefficients U I degree b n v y) =
      ∑ i : Fin (n + 1), if i.1 ≤ labeledCommonDepth n x.2 y.2 then
        ∑ j : SpinTensorIndex I degree, (v i j : ℝ) *
          spinTensorFeature U I degree a x.1 j * spinTensorFeature U I degree b y.1 j
        else 0 := by
  classical
  rw [tensorLeafCoefficients, tensorLeafCoefficients, featureCoefficients_diagonal
    (treeFeatureTag n x.2) (treeFeatureTag n y.2)
    (fun i j h => ((treeFeatureTag_cross n x.2 y.2 i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.1 ≤ labeledCommonDepth n x.2 y.2
  · simp only [hi, ite_true]
    apply Finset.sum_congr rfl
    intro j _
    have hs : (NNReal.sqrt (v i j) : ℝ) ^ 2 = (v i j : ℝ) :=
      by exact_mod_cast NNReal.sq_sqrt (v i j)
    calc
      _ = (NNReal.sqrt (v i j) : ℝ) ^ 2 *
          spinTensorFeature U I degree a x.1 j * spinTensorFeature U I degree b y.1 j := by ring
      _ = _ := by rw [hs]
  · simp only [hi, ite_false, Finset.sum_const_zero]

private lemma tensorLeafCoefficients_zero_cross {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (a : Fin k → ℝ) (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLeafCoefficients U I degree a n v x)
      (tensorLeafCoefficients U I degree 0 n v y) =
        cylinderCross (tensorLeafCoefficients U I degree 0 n v x)
          (tensorLeafCoefficients U I degree 0 n v y) ∧
    cylinderCross (tensorLeafCoefficients U I degree 0 n v x)
      (tensorLeafCoefficients U I degree a n v y) =
        cylinderCross (tensorLeafCoefficients U I degree 0 n v x)
          (tensorLeafCoefficients U I degree 0 n v y) := by
  simp_rw [tensorLeafCoefficients_mixed_cross]
  constructor <;> apply Finset.sum_congr rfl <;> intro i _
  all_goals
    split_ifs
    · apply Finset.sum_congr rfl
      intro j _
      cases j <;> simp [spinTensorFeature]
    · rfl

/-- The linear enrichment contributes no covariance to the increment
obtained by removing all monomial amplitudes. The remaining covariance
is bounded by the sum of their squared amplitudes, independently of depth. -/
lemma tensorPath_monomial_increment_cross_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (a : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (x y : Spin N × LabeledLeaf n) :
    let A := tensorLeafCoefficients U I degree a n (fun i => tensorPathProfile I degree n r h i)
    let C := tensorLeafCoefficients U I degree 0 n (fun i => tensorPathProfile I degree n r h i)
    |cylinderCross (A x - C x) (C y)| ≤ ∑ j, a j ^ 2 ∧
      |cylinderCross (A x - C x) (A y)| ≤ ∑ j, a j ^ 2 := by
  intro A C
  have hz := tensorLeafCoefficients_zero_cross U I degree a n
    (fun i => tensorPathProfile I degree n r h i) x y
  constructor
  · rw [cylinderCross_sub_left, hz.1, sub_self, abs_zero]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · rw [cylinderCross_sub_left, hz.2]
    dsimp only [A, C]
    rw [tensorPathProfile_covariance U I degree a n r h hh h0,
      tensorPathProfile_covariance U I degree 0 n r h hh h0]
    simp only [Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
      Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    calc
      _ ≤ ∑ j, |a j ^ 2 * (∏ b, projectedOverlap U (I b) x.1 y.1 ^ degree j b) *
          treeOverlap n x.2 y.2 ^ r j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, a j ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_pow,
          abs_of_nonneg (treeOverlap_mem n x.2 y.2).1]
        have hs := spectralMonomial_abs_le_one U I (degree j) x.1 y.1
        have ht : treeOverlap n x.2 y.2 ^ r j ≤ 1 :=
          pow_le_one₀ (treeOverlap_mem n x.2 y.2).1 (treeOverlap_mem n x.2 y.2).2
        have ht0 : 0 ≤ treeOverlap n x.2 y.2 ^ r j := pow_nonneg (treeOverlap_mem n x.2 y.2).1 _
        calc
          _ ≤ a j ^ 2 * 1 * 1 := mul_le_mul
            (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) ht ht0 (by positivity)
          _ = _ := by ring

theorem tensorPathLogMean_monomial_cost {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (a : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν) :
    let v := fun i : Fin (n + 1) => tensorPathProfile I degree n r h i
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp
        (H x + cylinderField (tensorLeafCoefficients U I degree a n v x) g) ∂ν) ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp
        (H x + cylinderField (tensorLeafCoefficients U I degree 0 n v x) g) ∂ν) ∂gaussianCoordinates| ≤
      2 * ∑ j, a j ^ 2 := by
  intro v
  exact countable_cylinder_log_mean_compare ν H hH _ _
    (tensorPathProfile_variance_cap U I degree 0 n r h hh h0)
    (tensorPathProfile_variance_cap U I degree a n r h hh h0)
    (fun x y => (tensorPath_monomial_increment_cross_le U I degree a n r h hh h0 x y).1)
    (fun x y => (tensorPath_monomial_increment_cross_le U I degree a n r h hh h0 x y).2)

theorem abs_tensorPathPressure_sub_zero_amplitude_le {N m k : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (a : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    let v := tensorPathProfile I degree n r h
    |tensorEnrichedPressure eig U c I degree a n b (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure eig U c I degree 0 n b (fun i => v (i + 1)) (v 0)| ≤
      2 * (N : ℝ)⁻¹ * ∑ j, a j ^ 2 := by
  intro v
  have hA := tensorFlatLog_integrable eig U c I degree a n b v
  have hC := tensorFlatLog_integrable eig U c I degree 0 n b v
  have hi := norm_integral_le_of_norm_le_const
    (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (f := fun T => (∫ g, tensorFlatLog eig U c I degree a n v (T, g) ∂gaussianCoordinates) -
      ∫ g, tensorFlatLog eig U c I degree 0 n v (T, g) ∂gaussianCoordinates)
    (C := 2 * ∑ j, a j ^ 2) (ae_of_all _ fun T => by
      simpa only [Real.norm_eq_abs, tensorFlatLog] using
        tensorPathLogMean_monomial_cost U I degree a n r h hh h0
          (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
          (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1)
          (finite_spin_base_exp_integrable _ (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)))
  rw [tensorEnrichedPressure_eq_flat_mean hN eig U c I degree a n b v hb,
    tensorEnrichedPressure_eq_flat_mean hN eig U c I degree 0 n b v hb,
    ← mul_sub, ← integral_sub hA.integral_prod_left hC.integral_prod_left, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have hbnd : |∫ T, ((∫ g, tensorFlatLog eig U c I degree a n v (T, g) ∂gaussianCoordinates) -
      ∫ g, tensorFlatLog eig U c I degree 0 n v (T, g) ∂gaussianCoordinates)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n))| ≤ 2 * ∑ j, a j ^ 2 := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi
  exact (mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq (by ring)

/-- The paper's finite monomial perturbation changes the enriched mean
pressure by at most `8 e_N²`, uniformly in the rotation and tree depth. -/
theorem tensorPerturbationPressure_cost {N m : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (n : ℕ) (r : Fin N → ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    let v := tensorPathProfile I degree n r h
    |tensorEnrichedPressure eig U c I degree (tensorPerturbationAmplitude N u) n b
        (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure eig U c I degree 0 n b (fun i => v (i + 1)) (v 0)| ≤
      8 * perturbationScale N ^ 2 := by
  intro v
  have hc := abs_tensorPathPressure_sub_zero_amplitude_le hN eig c U I degree
    (tensorPerturbationAmplitude N u) n r b hb h hh h0
  have hs := mul_le_mul_of_nonneg_left (tensorPerturbationAmplitude_square_sum_le N u hu)
    (show 0 ≤ 2 * (N : ℝ)⁻¹ by positivity)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : 2 * (N : ℝ)⁻¹ * (4 * N * perturbationScale N ^ 2) =
      8 * perturbationScale N ^ 2 := by field_simp; ring
  exact hc.trans (hs.trans_eq he)

end InvariantIsing

end

end OAI

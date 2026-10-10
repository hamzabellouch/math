import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationCost

namespace OAI

/-! A continuous covariance modulus in the actual Gaussian perturbation amplitudes. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma spinTensorFeature_mixed_amplitude_covariance {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (a b : Fin k → ℝ) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree a σ i * spinTensorFeature U I degree b τ i) =
      (site : ℝ) * (∑ i, spinValue (σ i) * spinValue (τ i)) +
        ∑ j, (monomial j : ℝ) * a j * b j *
          ∏ s, projectedOverlap U (I s) σ τ ^ degree j s := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, spinTensorFeature]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (monomial j : ℝ) * a j * b j *
          ∑ v : SpectralTensorIndex I (degree j),
            spectralMonomialFeature U I (degree j) σ v *
              spectralMonomialFeature U I (degree j) τ v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by rw [spectralMonomialFeature_cross]

lemma tensorPath_amplitude_increment_cross_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (a b c : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (x y : Spin N × LabeledLeaf n) :
    let A := fun w => tensorLeafCoefficients U I degree w n
      (fun i => tensorPathProfile I degree n r h i)
    |cylinderCross (A a x - A b x) (A c y)| ≤ ∑ j, |a j - b j| * |c j| := by
  intro A
  let L := fun i : Fin (n + 1) => ∑ j,
    (varianceIncrement (monomialPath n (r j)) i : ℝ) * |a j - b j| * |c j|
  let K := fun i : Fin (n + 1) => ∑ j,
    (varianceIncrement (monomialPath n (r j)) i : ℝ) * (a j - b j) * c j *
      ∏ s, projectedOverlap U (I s) x.1 y.1 ^ degree j s
  have hL (i : Fin (n + 1)) : 0 ≤ L i := by
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have he : cylinderCross (A a x - A b x) (A c y) =
      ∑ i : Fin (n + 1), if i.1 ≤ labeledCommonDepth n x.2 y.2 then K i else 0 := by
    rw [cylinderCross_sub_left]
    dsimp only [A]
    rw [tensorLeafCoefficients_mixed_cross, tensorLeafCoefficients_mixed_cross,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 ≤ labeledCommonDepth n x.2 y.2
    · simp only [hi, ite_true, tensorPathProfile, spinTensorFeature_mixed_amplitude_covariance,
        add_sub_add_left_eq_sub, K]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp only [hi, ite_false, sub_self]
  have hK (i : Fin (n + 1)) : |K i| ≤ L i := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (spectralMonomial_abs_le_one U I (degree j) x.1 y.1)
      (mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (abs_nonneg _)) (abs_nonneg _))).trans_eq
      (mul_one _)
  rw [he]
  calc
    _ ≤ ∑ i : Fin (n + 1), |if i.1 ≤ labeledCommonDepth n x.2 y.2 then K i else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (n + 1), L i := Finset.sum_le_sum fun i _ => by
      split_ifs
      · exact hK i
      · simpa only [abs_zero] using hL i
    _ ≤ ∑ j, |a j - b j| * |c j| := by
      dsimp only [L]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro j _
      simp_rw [mul_assoc]
      rw [← Finset.sum_mul]
      exact (mul_le_mul_of_nonneg_right (monomialVarianceIncrement_sum_le n (r j))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (one_mul _)

def tensorAmplitudeModulus {k : ℕ} (a b : Fin k → ℝ) : ℝ :=
  ∑ j, |a j - b j| * (|a j| + |b j|)

lemma tensorPathLogMean_amplitude_comparison {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (a b : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν) :
    let v := fun i : Fin (n + 1) => tensorPathProfile I degree n r h i
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp
        (H x + cylinderField (tensorLeafCoefficients U I degree a n v x) g) ∂ν) ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp
        (H x + cylinderField (tensorLeafCoefficients U I degree b n v x) g) ∂ν) ∂gaussianCoordinates| ≤
      2 * tensorAmplitudeModulus a b := by
  intro v
  apply countable_cylinder_log_mean_compare ν H hH _ _
    (tensorPathProfile_variance_cap U I degree b n r h hh h0)
    (tensorPathProfile_variance_cap U I degree a n r h hh h0)
  · intro x y
    apply (tensorPath_amplitude_increment_cross_le U I degree a b b n r h x y).trans
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _)
  · intro x y
    apply (tensorPath_amplitude_increment_cross_le U I degree a b a n r h x y).trans
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (abs_nonneg _)) (abs_nonneg _)


lemma tensorPathPressure_amplitude_comparison {N m k : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (a a' : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    let v := tensorPathProfile I degree n r h
    |tensorEnrichedPressure eig U c I degree a n b (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure eig U c I degree a' n b (fun i => v (i + 1)) (v 0)| ≤
      2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus a a' := by
  intro v
  have hA := tensorFlatLog_integrable eig U c I degree a n b v
  have hC := tensorFlatLog_integrable eig U c I degree a' n b v
  have hi := norm_integral_le_of_norm_le_const
    (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (f := fun T => (∫ g, tensorFlatLog eig U c I degree a n v (T, g) ∂gaussianCoordinates) -
      ∫ g, tensorFlatLog eig U c I degree a' n v (T, g) ∂gaussianCoordinates)
    (C := 2 * tensorAmplitudeModulus a a') (ae_of_all _ fun T => by
      simpa only [Real.norm_eq_abs, tensorFlatLog] using
        tensorPathLogMean_amplitude_comparison U I degree a a' n r h hh h0
          (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
          (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1)
          (finite_spin_base_exp_integrable _ (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)))
  rw [tensorEnrichedPressure_eq_flat_mean hN eig U c I degree a n b v hb,
    tensorEnrichedPressure_eq_flat_mean hN eig U c I degree a' n b v hb,
    ← mul_sub, ← integral_sub hA.integral_prod_left hC.integral_prod_left, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have hbnd : |∫ T, ((∫ g, tensorFlatLog eig U c I degree a n v (T, g) ∂gaussianCoordinates) -
      ∫ g, tensorFlatLog eig U c I degree a' n v (T, g) ∂gaussianCoordinates)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n))| ≤ 2 * tensorAmplitudeModulus a a' := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi
  exact (mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq (by ring)

end InvariantIsing

end

end OAI

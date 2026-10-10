import OAI.Probability.InvariantIsing.Arrays.TensorAmplitudeComparison

namespace OAI

/-! Covariance changes from varying only the ordinary Gaussian site
increments, while the monomial perturbation remains fixed. -/
noncomputable section
open IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma tensorLeafCoefficients_profile_cross {N m k n : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (a b : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLeafCoefficients U I degree amp n a x)
      (tensorLeafCoefficients U I degree amp n b y) =
      ∑ i : Fin (n+1), if i.1 ≤ labeledCommonDepth n x.2 y.2 then
        ∑ j, (NNReal.sqrt (a i j) : ℝ)*(NNReal.sqrt (b i j) : ℝ)*
          spinTensorFeature U I degree amp x.1 j*spinTensorFeature U I degree amp y.1 j else 0 := by
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
    ring
  · simp only [hi, ite_false, Finset.sum_const_zero]

lemma tensorSite_increment_cross_le {N m k n : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (a b c : Fin (n+1) → ℝ≥0) (mono : Fin (n+1) → Fin k → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    let A := fun v => tensorLeafCoefficients U I degree amp n
      (fun i => tensorVarianceProfile I degree (v i) (mono i))
    |cylinderCross (A a x-A b x) (A c y)| ≤
      (N : ℝ)*∑ i, |(NNReal.sqrt (a i) : ℝ)-(NNReal.sqrt (b i) : ℝ)| *(NNReal.sqrt (c i) : ℝ) := by
  intro A
  let d := fun i => ((NNReal.sqrt (a i) : ℝ)-(NNReal.sqrt (b i) : ℝ))*(NNReal.sqrt (c i) : ℝ)
  have he : cylinderCross (A a x-A b x) (A c y) =
      ∑ i : Fin (n+1), if i.1 ≤ labeledCommonDepth n x.2 y.2 then
        d i * ∑ j : Fin N, spinValue (x.1 j)*spinValue (y.1 j) else 0 := by
    rw [cylinderCross_sub_left]
    dsimp only [A]
    rw [tensorLeafCoefficients_profile_cross, tensorLeafCoefficients_profile_cross,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 ≤ labeledCommonDepth n x.2 y.2
    · simp only [hi, ite_true, Fintype.sum_sum_type, tensorVarianceProfile, spinTensorFeature]
      rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [d]
      ring
    · simp only [hi, ite_false, sub_self]
  have hspin : |∑ j : Fin N, spinValue (x.1 j)*spinValue (y.1 j)| ≤ N := by
    calc
      _ ≤ ∑ j : Fin N, |spinValue (x.1 j)*spinValue (y.1 j)| := Finset.abs_sum_le_sum_abs _ _
      _ = N := by simp [abs_mul, abs_spinValue]
  rw [he, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.1 ≤ labeledCommonDepth n x.2 y.2
  · simp only [hi, ite_true, abs_mul, d,
      abs_of_nonneg (NNReal.coe_nonneg (NNReal.sqrt (c i)))]
    nlinarith [mul_le_mul_of_nonneg_left hspin
      (mul_nonneg (abs_nonneg ((NNReal.sqrt (a i) : ℝ)-(NNReal.sqrt (b i) : ℝ)))
        (NNReal.coe_nonneg (NNReal.sqrt (c i))))]
  · simp only [hi, ite_false, abs_zero]
    positivity

end InvariantIsing

end

end OAI

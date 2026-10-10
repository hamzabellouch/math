import OAI.Probability.InvariantIsing.Arrays.TensorSiteComparison

namespace OAI

/-! Gaussian mean comparison for ordinary site-variance changes, with
an arbitrary integrable deterministic spin/leaf base. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma tensorSiteLogMean_modulus {N m k n : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (a b : Fin (n+1) → ℝ≥0) (mono : Fin (n+1) → Fin k → ℝ≥0)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν) :
    let F := fun v (z : ℕ → ℝ) => Real.log (∫ x, Real.exp (H x+
      cylinderField (tensorLeafCoefficients U I d amp n
        (fun i => tensorVarianceProfile I d (v i) (mono i)) x) z) ∂ν)
    |(∫ z, F a z ∂gaussianCoordinates)-∫ z, F b z ∂gaussianCoordinates| ≤
      2*((N : ℝ)*∑ i, |(NNReal.sqrt (a i) : ℝ)-(NNReal.sqrt (b i) : ℝ)| *
        ((NNReal.sqrt (a i) : ℝ)+(NNReal.sqrt (b i) : ℝ))) := by
  intro F
  let M := ∑ i, |(NNReal.sqrt (a i) : ℝ)-(NNReal.sqrt (b i) : ℝ)| *
    ((NNReal.sqrt (a i) : ℝ)+(NNReal.sqrt (b i) : ℝ))
  let A := fun (v : Fin (n+1) → ℝ≥0) => tensorLeafCoefficients U I d amp n
    (fun i => tensorVarianceProfile I d (v i) (mono i))
  have hc (e : Fin (n+1) → ℝ≥0) (he : e=a ∨ e=b) (x y : Spin N × LabeledLeaf n) :
      |cylinderCross (A a x-A b x) (A e y)| ≤ (N : ℝ)*M := by
    refine (tensorSite_increment_cross_le U I d amp a b e mono x y).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rcases he with rfl | rfl
    · exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
    · exact le_add_of_nonneg_left (NNReal.coe_nonneg _)
  exact countable_cylinder_log_mean_compare ν H hH (A a) (A b)
    (tensorLeafCoefficients_variance_le U I d amp n b mono)
    (tensorLeafCoefficients_variance_le U I d amp n a mono)
    (hc b (Or.inr rfl)) (hc a (Or.inl rfl))

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Arrays.TensorRotationCovariance
import OAI.Probability.InvariantIsing.Arrays.PerturbationMeasurability

namespace OAI

/-! Flat Gaussian coefficients for root and finite-depth tensor marks. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- Level zero is the common root mark. Positive levels encode the
corresponding ancestor prefix of the labeled leaf. -/
def tensorLeafCoefficients {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  featureCoefficients (treeFeatureTag n x.2)
    (fun i : Fin (n + 1) × SpinTensorIndex I degree =>
      (NNReal.sqrt (v i.1 i.2) : ℝ) * spinTensorFeature U I degree amplitude x.1 i.2)

lemma tensorLeafCoefficients_cross {N m k : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLeafCoefficients U I degree amplitude n v x)
      (tensorLeafCoefficients V I degree amplitude n v y) =
      ∑ i : Fin (n + 1), if i.1 ≤ labeledCommonDepth n x.2 y.2 then
        ∑ j : SpinTensorIndex I degree, (v i j : ℝ) *
          spinTensorFeature U I degree amplitude x.1 j * spinTensorFeature V I degree amplitude y.1 j
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
          spinTensorFeature U I degree amplitude x.1 j *
            spinTensorFeature V I degree amplitude y.1 j := by ring
      _ = _ := by rw [hs]
  · simp only [hi, ite_false, Finset.sum_const_zero]

lemma tensorLeafCoefficients_variance_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (x : Spin N × LabeledLeaf n) :
    (tensorLeafCoefficients U I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)) x).sum (fun _ c => c ^ 2) ≤
      ∑ i, ((site i : ℝ) * N + ∑ j, (monomial i j : ℝ) * amplitude j ^ 2) := by
  rw [← cylinderCross_self, tensorLeafCoefficients_cross]
  simp only [labeledCommonDepth_self,
    show ∀ i : Fin (n + 1), i.1 ≤ n from fun i => Nat.le_of_lt_succ i.isLt, ite_true]
  apply Finset.sum_le_sum
  intro i _
  simpa only [pow_two, mul_assoc] using
    spinTensorFeature_variance_le U I degree amplitude (site i) (monomial i) x.1

lemma cylinderCross_sub_left (a b c : ℕ →₀ ℝ) :
    cylinderCross (a - b) c = cylinderCross a c - cylinderCross b c := by
  have h := cylinderCross_add_left (a - b) b c
  rw [sub_add_cancel] at h
  linarith

/-- The full root/ancestor tensor increment has a uniform covariance
modulus, independently of the pair of cascade leaves. -/
theorem tensorLeafCoefficients_increment_cross_le {N m k : ℕ} (hN : 0 < N)
    (U V W : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    let A := fun R => tensorLeafCoefficients (specialRotation R) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i))
    |cylinderCross (A U x - A V x) (A W y)| ≤
      (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
        ∑ a, (degree j a : ℝ)) * frobeniusDistance U V := by
  intro A
  let L := fun i : Fin (n + 1) => ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
    ∑ a, (degree j a : ℝ)
  let Q := fun i : Fin (n + 1) => ∑ j : SpinTensorIndex I degree,
    (tensorVarianceProfile I degree (site i) (monomial i) j : ℝ) *
      (spinTensorFeature (specialRotation U) I degree amplitude x.1 j -
        spinTensorFeature (specialRotation V) I degree amplitude x.1 j) *
          spinTensorFeature (specialRotation W) I degree amplitude y.1 j
  have hL (i : Fin (n + 1)) : 0 ≤ L i := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hQ (i : Fin (n + 1)) : |Q i| ≤ L i * frobeniusDistance U V :=
    spinTensorFeature_increment_covariance_le hN U V W I degree amplitude (site i) (monomial i) x.1 y.1
  have he : cylinderCross (A U x - A V x) (A W y) =
      ∑ i : Fin (n + 1), if i.1 ≤ labeledCommonDepth n x.2 y.2 then Q i else 0 := by
    rw [cylinderCross_sub_left]
    dsimp only [A]
    rw [tensorLeafCoefficients_cross, tensorLeafCoefficients_cross, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 ≤ labeledCommonDepth n x.2 y.2
    · simp only [hi, ite_true]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp only [hi, ite_false, sub_self]
  rw [he]
  calc
    _ ≤ ∑ i : Fin (n + 1), |if i.1 ≤ labeledCommonDepth n x.2 y.2 then Q i else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (n + 1), L i * frobeniusDistance U V := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact hQ i
      · simp only [abs_zero]
        exact mul_nonneg (hL i) (show 0 ≤ frobeniusDistance U V from Real.sqrt_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Arrays.TensorLeafCoefficients
import OAI.Probability.InvariantIsing.Gaussian.CountableGaussianComparison
import OAI.Probability.InvariantIsing.Gaussian.GaussianBaseComparison
import OAI.Probability.InvariantIsing.Pressure.PressureLipschitz

namespace OAI

/-! Gaussian mean rotation comparison on the concrete countable tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The Gaussian part of the disorder-averaged leaf partition has a
uniform rotation modulus for every countable probability leaf prior. -/
theorem tensorLeafGaussianMean_abs_sub_le {N m k : ℕ} (hN : 0 < N)
    (U V : SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (n : ℕ)
    (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν) :
    let A := fun R => tensorLeafCoefficients (specialRotation R) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i))
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A U x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A V x) g) ∂ν)
        ∂gaussianCoordinates| ≤
      2 * (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
        ∑ a, (degree j a : ℝ)) * frobeniusDistance U V := by
  intro A
  have h := countable_cylinder_log_mean_compare ν H hH (A U) (A V)
    (tensorLeafCoefficients_variance_le (specialRotation V) I degree amplitude n site monomial)
    (tensorLeafCoefficients_variance_le (specialRotation U) I degree amplitude n site monomial)
    (tensorLeafCoefficients_increment_cross_le hN U V V I degree amplitude n site monomial)
    (tensorLeafCoefficients_increment_cross_le hN U V U I degree amplitude n site monomial)
  simpa only [mul_assoc] using h

lemma finite_spin_base_exp_integrable {N n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν] (H : Spin N → ℝ) :
    Integrable (fun x : Spin N × LabeledLeaf n => Real.exp (H x.1)) ν := by
  classical
  apply (integrable_const (∑ σ : Spin N, Real.exp (H σ))).mono'
    (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Finset.single_le_sum (fun σ _ => (Real.exp_pos (H σ)).le) (Finset.mem_univ x.1))

/-- Both the deterministic quadratic term and the Gaussian tensor marks
have uniform rotation moduli for the actual countable leaf partition. -/
theorem tensorLeafLogMean_abs_sub_le {N m k : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U V : SpecialOrthogonal N)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν] :
    let H := fun R (x : Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation R) x.1 + fieldEnergy c x.1
    let A := fun R => tensorLeafCoefficients (specialRotation R) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i))
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H U x + cylinderField (A U x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H V x + cylinderField (A V x) g) ∂ν)
        ∂gaussianCoordinates| ≤
      (K * N + 2 * (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
        ∑ a, (degree j a : ℝ))) * frobeniusDistance U V := by
  intro H A
  have hi (R : SpecialOrthogonal N) : Integrable (fun x => Real.exp (H R x)) ν := by
    exact finite_spin_base_exp_integrable ν
      (fun σ => rotatedEnergy eig (specialRotation R) σ + fieldEnergy c σ)
  have hb := countable_cylinder_log_mean_base_compare ν (H U) (H V) (hi U) (hi V)
    (A U) (tensorLeafCoefficients_variance_le (specialRotation U) I degree amplitude n site monomial)
    (fun x => by
      simpa only [H, add_sub_add_right_eq_sub] using
        abs_rotatedEnergy_sub_rotation_le eig U V K hK heig x.1)
  have hg := tensorLeafGaussianMean_abs_sub_le hN U V I degree amplitude n site monomial ν
    (H V) (hi V)
  exact (abs_sub_le _ _ _).trans ((add_le_add hb hg).trans_eq (by ring))

end InvariantIsing

end

end OAI

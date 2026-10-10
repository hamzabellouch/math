import OAI.Probability.InvariantIsing.Fields.PriorTensorNamespace
import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalCGF

namespace OAI

/-! The actual fixed-prior Gibbs law and its spectral diagonal tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorNamespacedReference {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability ν (priorNamespacedHamiltonian eig c I degree amplitude v p)

instance priorNamespacedReference_probability {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) :
    IsProbabilityMeasure (priorNamespacedReference ν eig c I degree amplitude v p) :=
  gibbsProbability_probability _ _

lemma measurable_priorNamespacedReference {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (priorNamespacedReference ν eig c I degree amplitude v) :=
  measurable_gibbsProbability (ν := fun _ => ν) measurable_const
    (measurable_priorNamespacedHamiltonian eig c I degree amplitude v)

private lemma base_coefficient_exp_integrable_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (μ : Measure Ω) (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω → X → ℝ) (hH : Measurable (Function.uncurry H))
    (hi : ∀ ω, Integrable (fun x => Real.exp (H ω x)) ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (K : ℝ) (hb : ∀ ω x, (A ω x).sum (fun _ c => c^2) ≤ K) :
    ∀ᵐ p ∂μ.prod gaussianCoordinates,
      Integrable (fun x => Real.exp (H p.1 x+cylinderField (A p.1 x) p.2)) ν := by
  have : ∀ ω, IsProbabilityMeasure (ν.tilted (H ω)) :=
    fun ω => isProbabilityMeasure_tilted (hi ω)
  have hm : Measurable (fun ω => ν.tilted (H ω)) :=
    measurable_random_tilted_measure (ν := fun _ => ν) (H := Function.uncurry H) measurable_const hH
  have he := randomCoefficient_all_exp_ae (P := μ) hm A hA hb
  filter_upwards [he] with p hp
  have hi' := hp 1
  rw [integrable_tilted_iff (hi p.1)] at hi'
  simpa only [one_mul,smul_eq_mul,← Real.exp_add] using hi'

private lemma prior_base_measurable {N n : ℕ} (eig c : Fin N → ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1) p.2.1 + fieldEnergy c p.2.1) := by
  apply measurable_from_prod_countable_left
  intro x
  change Measurable (fun U : SpecialOrthogonal N =>
    rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1)
  unfold rotatedEnergy
  exact ((Finset.measurable_sum _ fun i _ =>
    ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul
      (1/2 : ℝ)).add_const _

private lemma prior_field_measurable {N m k n : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (fun p : (SpecialOrthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n v p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  exact measurable_tensorNamespacedFields_joint I degree amplitude n v x

lemma priorNamespaced_exp_integrable_ae {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) :
    ∀ᵐ p ∂μ.prod gaussianCoordinates,
      Integrable (fun x => Real.exp (priorNamespacedHamiltonian eig c I degree amplitude
        (fun i => tensorPathProfile I degree n r h i) p x)) ν := by
  exact base_coefficient_exp_integrable_ae μ ν
    (fun U x => rotatedEnergy eig (specialRotation U) x.1+fieldEnergy c x.1)
    (prior_base_measurable eig c)
    (fun U => finite_spin_base_exp_integrable ν
      (fun σ => rotatedEnergy eig (specialRotation U) σ+fieldEnergy c σ))
    (fun U => tensorNamespacedCoefficients (specialRotation U) I degree amplitude n
      (fun i => tensorPathProfile I degree n r h i))
    (prior_field_measurable I degree amplitude _) _
    (fun U x => tensorNamespacedPath_variance_le (specialRotation U) I degree amplitude n r h hh h0 x)

lemma prior_diagonal_cgf_eq_log_difference {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ) :
    ∀ᵐ p ∂μ.prod gaussianCoordinates,
      cgf (fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1) (I a) x.1 x.1)
        (priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
          c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p)
        (N*perturbationScale N*w) =
      priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p -
      priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p := by
  filter_upwards [priorNamespaced_exp_integrable_ae μ ν
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude r h hh h0] with p hp
  let H : Spin N × LabeledLeaf n → ℝ :=
    priorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
    c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p
  let Y := fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1) (I a) x.1 x.1
  have hbnd x : |(N*perturbationScale N*w)*Y x| ≤ |N*perturbationScale N*w| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (projectedOverlap_abs_le_one _ _ _ _)
      (abs_nonneg _)).trans_eq (mul_one _)
  have hi : Integrable (fun x => Real.exp (H x+(N*perturbationScale N*w)*Y x)) ν := by
    simpa only [add_comm] using integrable_exp_bounded_add (H := H) hp
      (measurable_of_countable (fun x => (N*perturbationScale N*w)*Y x))
      (fun x => (le_abs_self _).trans (hbnd x))
  have he : (fun x => H x+(N*perturbationScale N*w)*Y x) =
      priorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p := by
    funext x
    dsimp only [H,Y,priorNamespacedHamiltonian]
    rw [rotatedEnergy_diagonal_coordinate hN eig (specialRotation p.1) I v t a w x.1]
    ring
  change cgf Y (gibbsProbability ν H) _ = _
  rw [cgf_fold ν H Y _ hp hi,he]
  rfl

end InvariantIsing

end

end OAI

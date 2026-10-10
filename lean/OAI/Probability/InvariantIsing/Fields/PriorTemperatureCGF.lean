import OAI.Probability.InvariantIsing.Fields.PriorReplicaAverage
import OAI.Probability.InvariantIsing.Fields.PriorTensorMinimum
import OAI.Probability.InvariantIsing.Pressure.RandomBoundedDerivative

namespace OAI

/-! Temperature is a bounded tilt of the actual constrained-prior Gibbs
measure. The spectral and Gaussian perturbations stay fixed under the tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology NNReal
namespace InvariantIsing

lemma priorTemperatureHamiltonian_affine {N m k n : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (q : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) (t : ℝ) :
    priorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v t) c I degree amp q p =
      fun x => priorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0)
        c I degree amp q p x + t*rotatedEnergy eig (specialRotation p.1) x.1 := by
  funext x
  unfold priorNamespacedHamiltonian
  rw [rotatedEnergy_diagonalPerturbation hN, rotatedEnergy_diagonalPerturbation hN]
  ring

lemma measurable_priorTemperatureObservable {N n : ℕ} (eig : Fin N → ℝ) :
    Measurable (fun p : (SpecialOrthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1.1) p.2.1) := by
  apply measurable_from_prod_countable_left
  intro x
  unfold rotatedEnergy
  exact (Finset.measurable_sum _ fun i _ =>
    ((measurable_specialRotation_eval (spinVector x.1) i).comp measurable_fst).pow_const 2
      |>.const_mul (eig i)).const_mul _

lemma priorTemperature_reference_fold {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂μ.prod gaussianCoordinates,
      (priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I v 0) c I degree amp
        (fun i => tensorPathProfile I degree n r h i) p).tilted
        (fun x => t*rotatedEnergy eig (specialRotation p.1) x.1) =
      priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I v t) c I degree amp
        (fun i => tensorPathProfile I degree n r h i) p := by
  filter_upwards [priorNamespaced_exp_integrable_ae μ ν (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp r h hh h0, priorNamespaced_exp_integrable_ae μ ν
      (diagonalPerturbedEigenvalues eig I v t) c I degree amp r h hh h0] with p hp ht
  let H : Spin N × LabeledLeaf n → ℝ := priorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp (fun i => tensorPathProfile I degree n r h i) p
  let G := fun x : Spin N × LabeledLeaf n => t*rotatedEnergy eig (specialRotation p.1) x.1
  have he := priorTemperatureHamiltonian_affine (n := n) hN eig c I v degree amp
    (fun i => tensorPathProfile I degree n r h i) p t
  have hH : Integrable (fun x => Real.exp (H x)) ν := hp
  have hi : Integrable (fun x => Real.exp (H x+G x)) ν := by
    rw [he] at ht
    exact ht
  change (gibbsProbability ν H).tilted G = gibbsProbability ν _
  rw [he, gibbsProbability_eq_tilted ν H hH,
    gibbsProbability_eq_tilted ν (fun x => H x+G x) hi, tilted_tilted hH G]
  rfl

lemma priorTemperatureCGF_eq_log_difference {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (t : ℝ) :
    ∀ᵐ p ∂μ.prod gaussianCoordinates,
      cgf (fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation p.1) x.1)
        (priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I v 0) c I degree amp
          (fun i => tensorPathProfile I degree n r h i) p) t =
      priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I v t) c I degree amp
        (fun i => tensorPathProfile I degree n r h i) p -
      priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I v 0) c I degree amp
        (fun i => tensorPathProfile I degree n r h i) p := by
  filter_upwards [priorNamespaced_exp_integrable_ae μ ν (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp r h hh h0, priorNamespaced_exp_integrable_ae μ ν
      (diagonalPerturbedEigenvalues eig I v t) c I degree amp r h hh h0] with p hp ht
  let H : Spin N × LabeledLeaf n → ℝ := priorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I v 0)
    c I degree amp (fun i => tensorPathProfile I degree n r h i) p
  let Y := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation p.1) x.1
  have he := priorTemperatureHamiltonian_affine (n := n) hN eig c I v degree amp
    (fun i => tensorPathProfile I degree n r h i) p t
  have hi : Integrable (fun x => Real.exp (H x+t*Y x)) ν := by
    rw [he] at ht
    exact ht
  change cgf Y (gibbsProbability ν H) t = _
  rw [cgf_fold ν H Y t hp hi]
  rw [show (fun x => H x+t*Y x) = priorNamespacedHamiltonian
    (diagonalPerturbedEigenvalues eig I v t) c I degree amp
    (fun i => tensorPathProfile I degree n r h i) p from he.symm]
  rfl

lemma priorNamespacedLog_integrable (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m k n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (site : Fin (n+1) → ℝ≥0) (monomial : Fin (n+1) → Fin k → ℝ≥0) :
    Integrable (priorNamespacedLog ν eig c I degree amp
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)))
      (μ.prod gaussianCoordinates) := by
  obtain ⟨C,hC,hv⟩ := priorTensorLog_variance hhaar hgauss
  have hK : 0 < 1+∑ i, |eig i| := by positivity
  have he : ∀ i, |eig i| ≤ 1+∑ i, |eig i| := fun i => by
    have hi := Finset.single_le_sum (f := fun j => |eig j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  exact (priorNamespacedLog_moments μ ν eig c I degree amp _
    (hv N hN μ inferInstance hμ m k n ν inferInstance eig c _ hK he I degree amp site monomial).1).1.integrable
      (by norm_num)

lemma priorNamespacedLog_integral {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (q : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    (∫ p, priorNamespacedLog ν eig c I degree amp q p ∂μ.prod gaussianCoordinates) =
      ∫ p, priorTensorLog ν eig c I degree amp q p ∂μ.prod gaussianCoordinates :=
  (priorNamespacedLog_law μ ν eig c I degree amp q).integral_eq.trans
    (integral_map (measurable_priorTensorLog ν eig c I degree amp q).aemeasurable
      aestronglyMeasurable_id)

end InvariantIsing

end

end OAI

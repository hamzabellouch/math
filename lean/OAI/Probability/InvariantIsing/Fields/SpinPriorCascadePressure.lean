import OAI.Probability.InvariantIsing.Arrays.TensorFieldDerivativeIntegrability
import OAI.Probability.InvariantIsing.Fields.PriorTemperatureCGF
import OAI.Probability.InvariantIsing.Pressure.ThermalPressure

namespace OAI

/-! The actual cascade-enriched pressure for a deterministic spin prior.
Normalized magnetization slices are allowed, while the cascade remains
quenched and is averaged only after taking the logarithm. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

def spinPriorNamespacedLog {N m k n : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (p : TensorFlatDisorder N n) : ℝ :=
  priorNamespacedLog (labeledSpinReference n π p.1.2) eig c I degree amp
    (fun i => tensorPathProfile I degree n r h i) (p.1.1,p.2)

def spinPriorNamespacedReference {N m k n : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (p : TensorFlatDisorder N n) : Measure (Spin N × LabeledLeaf n) :=
  priorNamespacedReference (labeledSpinReference n π p.1.2) eig c I degree amp
    (fun i => tensorPathProfile I degree n r h i) (p.1.1,p.2)

def spinPriorMeanPressure {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) : ℝ :=
  (N : ℝ)⁻¹*(∫ p, spinPriorNamespacedLog π eig c I degree amp r h p
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)-h n/2

lemma measurable_spinPriorNamespacedLog {N m k n : ℕ}
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (spinPriorNamespacedLog (n := n) π eig c I degree amp r h) := by
  have hν : Measurable (fun p : TensorFlatDisorder N n => labeledSpinReference n π p.1.2) :=
    (measurable_labeledSpinReference_general n π).comp measurable_fst.snd
  exact (measurable_random_referencePartition hν
    (measurable_tensorNamespacedHamiltonian eig c I degree amp n r h)).log

lemma measurable_spinPriorNamespacedReference {N m k n : ℕ}
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (spinPriorNamespacedReference (n := n) π eig c I degree amp r h) := by
  have hν : Measurable (fun p : TensorFlatDisorder N n => labeledSpinReference n π p.1.2) :=
    (measurable_labeledSpinReference_general n π).comp measurable_fst.snd
  exact measurable_gibbsProbability hν (measurable_tensorNamespacedHamiltonian eig c I degree amp n r h)

instance spinPriorNamespacedReference_probability {N m k n : ℕ}
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (p : TensorFlatDisorder N n) :
    IsProbabilityMeasure (spinPriorNamespacedReference π eig c I degree amp r h p) := by
  unfold spinPriorNamespacedReference
  infer_instance

lemma spinPriorDeterministicLog_abs_le {N n : ℕ}
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (ω : SpecialOrthogonal N × LabeledTree n) :
    |Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
      (tensorDeterministicEnergy eig c n ω x) ∂labeledSpinReference n π ω.2)| ≤
      (∑ i, |eig i|)*N/2+∑ i, |c i| := by
  let ν := labeledSpinReference n π ω.2
  let H := tensorDeterministicEnergy eig c n ω
  have hH : Integrable (fun x => Real.exp (H x)) ν := finite_spin_base_exp_integrable ν
    (fun σ => rotatedEnergy eig (specialRotation ω.1) σ+fieldEnergy c σ)
  have hbound (x : Spin N × LabeledLeaf n) : |H x| ≤ (∑ i, |eig i|)*N/2+∑ i, |c i| := by
    have he := abs_rotatedEnergy_le eig (specialRotation ω.1) (∑ i, |eig i|)
      (fun i => Finset.single_le_sum (fun j _ => abs_nonneg (eig j)) (Finset.mem_univ i)) x.1
    have hf : |fieldEnergy c x.1| ≤ ∑ i, |c i| := by
      simpa only [fieldEnergy,zero_mul,Finset.sum_const_zero,sub_zero] using
        abs_fieldEnergy_sub_le c (fun _ => 0) x.1
    exact (abs_add_le _ _).trans (add_le_add he hf)
  have hb := logMean_abs_sub_le ν (F := H) (G := fun _ => 0) (b := 1) (by norm_num)
    (by simpa only [one_mul] using hH)
    (by simpa only [mul_zero,Real.exp_zero] using (integrable_const (1 : ℝ)))
    (fun x => by simpa only [sub_zero] using hbound x)
  simpa only [logMean,one_mul,div_one,Real.exp_zero,integral_const,probReal_univ,
    one_smul,Real.log_one,sub_zero] using hb

lemma spinPriorDeterministicLog_integrable {N n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ) (b : ℕ → ℝ) :
    Integrable (fun ω : SpecialOrthogonal N × LabeledTree n => Real.log
      (∫ x, Real.exp (tensorDeterministicEnergy eig c n ω x) ∂labeledSpinReference n π ω.2))
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))) := by
  have hν : Measurable (fun ω : SpecialOrthogonal N × LabeledTree n => labeledSpinReference n π ω.2) :=
    (measurable_labeledSpinReference_general n π).comp measurable_snd
  apply integrable_of_measurable_abs_le
    (c := (∑ i, |eig i|)*N/2+∑ i, |c i|)
    ((measurable_random_referencePartition hν (measurable_tensorDeterministicEnergy eig c n)).log)
  exact spinPriorDeterministicLog_abs_le π eig c

theorem spinPriorNamespacedLog_integrable {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Integrable (spinPriorNamespacedLog (n := n) π eig c I degree amp r h)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  have hν : Measurable (fun ω : SpecialOrthogonal N × LabeledTree n => labeledSpinReference n π ω.2) :=
    (measurable_labeledSpinReference_general n π).comp measurable_snd
  exact randomCoefficient_log_partition_integrable hν (tensorDeterministicEnergy eig c n)
    (measurable_tensorDeterministicEnergy eig c n)
    (fun ω => finite_spin_base_exp_integrable (labeledSpinReference n π ω.2)
      (fun σ => rotatedEnergy eig (specialRotation ω.1) σ+fieldEnergy c σ))
    (spinPriorDeterministicLog_integrable μ π eig c b)
    (fun ω => tensorNamespacedCoefficients (specialRotation ω.1) I degree amp n
      (fun i => tensorPathProfile I degree n r h i))
    (measurable_tensorNamespacedPathFields I degree amp n r h)
    (fun ω x => tensorNamespacedPath_variance_le (specialRotation ω.1) I degree amp n r h hh h0 x)

end InvariantIsing

end

end OAI

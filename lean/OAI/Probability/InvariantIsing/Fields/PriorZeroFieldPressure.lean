import OAI.Probability.InvariantIsing.Fields.PriorPerturbationCost
import OAI.Probability.InvariantIsing.Magnetic.RestrictedZeroTreeArrayLaw
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressure

namespace OAI

/-! The unperturbed fixed-prior pressure is exactly the physical constrained
pressure with its cube-mass constant removed. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma tensor_zero_field_zero_amplitude {N m k n : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (r : Fin k → ℕ)
    (x : Spin N × LabeledLeaf n) (z : ℕ → ℝ) :
    cylinderField (tensorLeafCoefficients U I degree 0 n
      (fun i => tensorPathProfile I degree n r (fun _ => 0) i) x) z = 0 := by
  rw [tensorLeafCoefficients, cylinderField_feature]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ _
  cases j <;> simp [tensorPathProfile, tensorVarianceProfile, spinTensorFeature,
    varianceIncrement_zero_path]

lemma priorTensorLog_zero_field {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (r : Fin k → ℕ)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) :
    priorTensorLog ν eig c I degree 0
      (fun i => tensorPathProfile I degree n r (fun _ => 0) i) p =
      finiteLogIntegral ν (fun x => rotatedEnergy eig (specialRotation p.1) x.1 + fieldEnergy c x.1) := by
  simp only [priorTensorLog, tensor_zero_field_zero_amplitude, add_zero, finiteLogIntegral]

lemma prior_zero_field_pressure {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) :
    priorPerturbationPressureMean μ ν eig c I t (fun _ => 0) 0 0 =
      (N : ℝ)⁻¹ * ∫ U, finiteLogIntegral ν
        (fun x => rotatedEnergy (fun i => t*eig i) (specialRotation U) x.1 + fieldEnergy c x.1) ∂μ := by
  have hamp : tensorPerturbationAmplitude N 0 = 0 := by
    ext j
    simp [tensorPerturbationAmplitude]
  have heig : diagonalPerturbedEigenvalues eig I 0 t = fun i => t*eig i := by
    ext i
    simp [diagonalPerturbedEigenvalues]
  simp only [priorPerturbationPressureMean, hamp, heig, priorTensorLog_zero_field]
  congr 1
  simpa only [probReal_univ, one_smul] using integral_fun_fst (μ := μ) (ν := gaussianCoordinates)
    (fun U : SpecialOrthogonal N => finiteLogIntegral ν
      (fun x => rotatedEnergy (fun i => t*eig i) (specialRotation U) x.1 + fieldEnergy c x.1))

lemma restricted_zero_field_pressure {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) :
    priorPerturbationPressureMean μ (restrictedZeroTreePrior S hS) eig c I t (fun _ => 0) 0 0 =
      (∫ U, restrictedRotatedPressure S (fun i => t*eig i) (specialRotation U) c ∂μ) -
        (N : ℝ)⁻¹*(Real.log S.card-N*Real.log 2) := by
  rw [prior_zero_field_pressure]
  let : IsProbabilityMeasure (labeledLeafLaw 0 (PUnit.unit : LabeledTree 0)) :=
    labeledLeafLaw_probability 0 PUnit.unit
  have he (U : SpecialOrthogonal N) : finiteLogIntegral (restrictedZeroTreePrior S hS)
      (fun x => rotatedEnergy (fun i => t*eig i) (specialRotation U) x.1 + fieldEnergy c x.1) =
      finiteLogIntegral (restrictedSpinPrior S hS : Measure (Spin N))
        (fun σ => rotatedEnergy (fun i => t*eig i) (specialRotation U) σ + fieldEnergy c σ) := by
    unfold restrictedZeroTreePrior labeledSpinReference finiteLogIntegral
    congr 1
    simpa only [probReal_univ, one_smul] using integral_fun_fst
      (μ := (restrictedSpinPrior S hS : Measure (Spin N))) (ν := labeledLeafLaw 0 PUnit.unit)
      (fun σ => Real.exp (rotatedEnergy (fun i => t*eig i) (specialRotation U) σ + fieldEnergy c σ))
  simp_rw [he, finiteLogIntegral_restrictedSpinPrior]
  let H := fun (U : SpecialOrthogonal N) (σ : Spin N) =>
    rotatedEnergy (fun i => t*eig i) (specialRotation U) σ + fieldEnergy c σ
  have hE (σ : Spin N) : Measurable (fun U => H U σ) :=
    ((Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector σ) i).pow_const 2).const_mul
        (t*eig i)).const_mul (1/2 : ℝ)).add_const _
  have hm : Measurable (fun U => restrictedSpinLog S (H U)) := by
    unfold restrictedSpinLog
    exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).log).sub_const _
  let B := (∑ i, |t*eig i|)*N/2 + ∑ i, |c i|
  have hb (U : SpecialOrthogonal N) (σ : Spin N) : |H U σ| ≤ B := by
    have hq := abs_rotatedEnergy_le (fun i => t*eig i) (specialRotation U)
      (∑ i, |t*eig i|)
      (fun i => Finset.single_le_sum (fun j _ => abs_nonneg (t*eig j)) (Finset.mem_univ i)) σ
    have hf := abs_fieldEnergy_sub_le c 0 σ
    simp only [fieldEnergy, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at hf
    exact (abs_add_le _ _).trans (add_le_add hq hf)
  have hi : Integrable (fun U => restrictedSpinLog S (H U)) μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable (B+|restrictedSpinLog S (fun _ => 0)|)
    apply ae_of_all
    intro U
    rw [Real.norm_eq_abs]
    have hh := abs_restrictedSpinLog_sub_le S hS (H U) (fun _ => 0) B
      (fun σ _ => by simpa only [sub_zero] using hb U σ)
    calc
      _ = |(restrictedSpinLog S (H U)-restrictedSpinLog S (fun _ => 0))+
          restrictedSpinLog S (fun _ => 0)| := by congr 1; ring
      _ ≤ |restrictedSpinLog S (H U)-restrictedSpinLog S (fun _ => 0)|+
          |restrictedSpinLog S (fun _ => 0)| := abs_add_le _ _
      _ ≤ _ := add_le_add hh le_rfl
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul, mul_sub]
  rw [← integral_const_mul]
  rfl

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Fields.PriorTensorReference
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRotationProbability
import OAI.Probability.InvariantIsing.Cavity.CavityOrientationProbability

namespace OAI

/-! The physical constrained Gibbs probability has the fixed-prior Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem priorTensorGibbs_law {N m k depth : ℕ}
    (ν : Measure (Spin N × LabeledLeaf depth)) [IsProbabilityMeasure ν]
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (v : Fin (depth+1) → SpinTensorIndex I degree → ℝ≥0)
    (H : Spin N × LabeledLeaf depth → ℝ) :
    gaussianCoordinates.map (fun z => gibbsProbability ν
      (fun x => H x+cylinderField (tensorLeafCoefficients U I degree amp depth v x) z)) =
    gaussianCoordinates.map (fun z => gibbsProbability ν
      (fun x => H x+cylinderField (tensorNamespacedCoefficients U I degree amp depth v x) z)) := by
  let X := Spin N × LabeledLeaf depth
  let G : (X → ℝ) → Measure X := fun f => gibbsProbability ν (fun x => H x+f x)
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2+p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  have hG : Measurable G := measurable_gibbsProbability (ν := fun _ => ν) measurable_const hm
  have hA : Measurable (fun z x => cylinderField (tensorLeafCoefficients U I degree amp depth v x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  have hC : Measurable (fun z x => cylinderField (tensorNamespacedCoefficients U I degree amp depth v x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  have hh := congrArg (fun μ : Measure (X → ℝ) => μ.map G)
    (tensorNamespacedFields_law U I degree amp depth v)
  simpa only [Measure.map_map hG hA,Measure.map_map hG hC,Function.comp_def,G] using hh

lemma restricted_orientation_probability_law {N m depth : ℕ} (hN : 0<N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (V : Orthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    gaussianCoordinates.map (fun z => restrictedRotationProbability S hS eig I u ((V,T),z)) =
      gaussianCoordinates.map (fun z => restrictedRotationProbability S hS eig I u
        (((cavitySpecialOrthogonal (cavityOrientationLift hN V⁻¹))⁻¹,T),z)) := by
  have hh := cavity_gibbs_probability_same_covariance
    (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (fun x => rotatedEnergy eig (matrixRotation V⁻¹) x.1)
    (cavityPerturbationCoefficients (matrixRotation V⁻¹) I u depth)
    (cavityPerturbationCoefficients (specialRotation (cavityOrientationLift hN V⁻¹)) I u depth)
    (fun x y => (cavityOrientationLift_perturbation_covariance hN V⁻¹ I u x y).symm)
  simp only [restrictedRotationProbability,inv_inv]
  unfold cavityRotationHamiltonian
  simp only [show matrixRotation (cavitySpecialOrthogonal (cavityOrientationLift hN V⁻¹)) =
    specialRotation (cavityOrientationLift hN V⁻¹) from rfl,cavityOrientationLift_energy]
  exact hh

lemma restricted_special_prior_probability_law {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (U : SpecialOrthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    gaussianCoordinates.map (fun z => restrictedRotationProbability S hS eig I u
      (((cavitySpecialOrthogonal U)⁻¹,T),z)) =
    gaussianCoordinates.map (fun z => priorNamespacedReference
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
      eig (fun _ => 0) I (fun j : Fin N => enumeratedSpectralDegree m j)
      (tensorPerturbationAmplitude N (fun j => u j))
      (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j) depth
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i) (U,z)) := by
  let degree := fun j : Fin N => enumeratedSpectralDegree m j
  let amp := tensorPerturbationAmplitude N (fun j : Fin N => u j)
  let v : Fin (depth+1) → SpinTensorIndex I degree → ℝ≥0 := fun i => tensorPathProfile I degree depth
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i
  have hh := priorTensorGibbs_law
    (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (specialRotation U) I degree amp v (fun x => rotatedEnergy eig (specialRotation U) x.1)
  simp only [restrictedRotationProbability,inv_inv,
    show matrixRotation (cavitySpecialOrthogonal U)=specialRotation U from rfl,priorNamespacedReference]
  unfold cavityRotationHamiltonian priorNamespacedHamiltonian
  simp only [fieldEnergy,zero_mul,Finset.sum_const_zero,add_zero]
  simpa only [cavityPerturbationCoefficients,degree,amp,v] using hh

theorem restricted_orientation_prior_probability_law {N m depth : ℕ} (hN : 0<N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (V : Orthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    gaussianCoordinates.map (fun z => restrictedRotationProbability S hS eig I u ((V,T),z)) =
    gaussianCoordinates.map (fun z => priorNamespacedReference
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
      eig (fun _ => 0) I (fun j : Fin N => enumeratedSpectralDegree m j)
      (tensorPerturbationAmplitude N (fun j => u j))
      (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j) depth
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i)
      (cavityOrientationLift hN V⁻¹,z)) :=
  (restricted_orientation_probability_law hN S hS V T eig I u).trans
    (restricted_special_prior_probability_law S hS (cavityOrientationLift hN V⁻¹) T eig I u)

end InvariantIsing

end

end OAI

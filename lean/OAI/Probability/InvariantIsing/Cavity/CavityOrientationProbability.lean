import OAI.Probability.InvariantIsing.Cavity.CavityProbabilityCovariance
import OAI.Probability.InvariantIsing.Cavity.CavityOrientationOverlap
import OAI.Probability.InvariantIsing.Cavity.CavityTensorProbabilityLaw

namespace OAI

/-! Orienting the eigenbasis preserves the whole random Gibbs probability,
and identifies it with the published-input tensor realization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityOrientationLift_perturbation_covariance {N m depth : ℕ}
    (hN : 0 < N) (U : Orthogonal N) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (x y : Spin N × LabeledLeaf depth) :
    cylinderCross (cavityPerturbationCoefficients (specialRotation (cavityOrientationLift hN U)) I u depth x)
      (cavityPerturbationCoefficients (specialRotation (cavityOrientationLift hN U)) I u depth y) =
    cylinderCross (cavityPerturbationCoefficients (matrixRotation U) I u depth x)
      (cavityPerturbationCoefficients (matrixRotation U) I u depth y) := by
  simp only [cavityPerturbationCoefficients_cross, cavityWeightedKernel,
    cavityPerturbationKernel, cavityOrientationLift_overlap]

theorem cavity_orientation_probability_law {N m depth : ℕ} (hN : 0 < N)
    (V : Orthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    gaussianCoordinates.map (fun z => cavityRotationProbability eig I u ((V,T),z)) =
      gaussianCoordinates.map (fun z => cavityRotationProbability eig I u
        (((cavitySpecialOrthogonal (cavityOrientationLift hN V⁻¹))⁻¹,T),z)) := by
  have hh := cavity_gibbs_probability_same_covariance
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun x => rotatedEnergy eig (matrixRotation V⁻¹) x.1)
    (cavityPerturbationCoefficients (matrixRotation V⁻¹) I u depth)
    (cavityPerturbationCoefficients (specialRotation (cavityOrientationLift hN V⁻¹)) I u depth)
    (fun x y => (cavityOrientationLift_perturbation_covariance hN V⁻¹ I u x y).symm)
  simp only [cavityRotationProbability, inv_inv]
  unfold cavityRotationHamiltonian
  simp only [show matrixRotation (cavitySpecialOrthogonal (cavityOrientationLift hN V⁻¹)) =
    specialRotation (cavityOrientationLift hN V⁻¹) from rfl, cavityOrientationLift_energy]
  exact hh

theorem cavity_orientation_tensor_probability_law {N m depth : ℕ} (hN : 0 < N)
    (V : Orthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    gaussianCoordinates.map (fun z => cavityRotationProbability eig I u ((V,T),z)) =
      gaussianCoordinates.map (fun z => tensorNamespacedReference eig (fun _ => 0) I
        (fun j : Fin N => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude N (fun j => u j)) depth
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0)
        ((cavityOrientationLift hN V⁻¹,T),z)) :=
  (cavity_orientation_probability_law hN V T eig I u).trans
    (cavity_rotation_tensor_probability_law (cavityOrientationLift hN V⁻¹) T eig I u)

end InvariantIsing

end

end OAI

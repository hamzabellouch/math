import OAI.Probability.InvariantIsing.Cavity.CavityGroupOverlapInvariant
import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCovarianceLaw
import OAI.Probability.InvariantIsing.Cavity.CavityOriginalFactor
import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalPerturbation

namespace OAI

/-! The actual Gaussian perturbation respects rotations inside every
base spectral group, after averaging over the Gaussian disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityGroup_diagonal_eigenvalues {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (lam v : Fin m → ℝ) (t : ℝ) :
    diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
      (cavitySpectralGroup (fun i => (e.symm i).1)) v t =
      fun i => t * lam (e.symm i).1 + 2 * perturbationScale N * v (e.symm i).1 := by
  funext i
  simp [diagonalPerturbedEigenvalues, cavitySpectralGroup]

theorem cavityGroupRotation_perturbed_energy {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a))
    (lam v : Fin m → ℝ) (t : ℝ) (σ : Spin N) :
    rotatedEnergy (diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
      (cavitySpectralGroup (fun i => (e.symm i).1)) v t)
      (matrixRotation (V * cavityGroupRotation k e W)⁻¹) σ =
    rotatedEnergy (diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
      (cavitySpectralGroup (fun i => (e.symm i).1)) v t) (matrixRotation V⁻¹) σ := by
  rw [cavityGroup_diagonal_eigenvalues]
  exact cavityGroupRotation_energy k e V W (fun a => t * lam a + 2 * perturbationScale N * v a) σ

theorem cavityGroupRotation_perturbation_covariance {N m depth : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a)) (u : ℕ → ℝ)
    (x y : Spin N × LabeledLeaf depth) :
    cylinderCross (cavityPerturbationCoefficients (matrixRotation (V * cavityGroupRotation k e W)⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1)) u depth x)
      (cavityPerturbationCoefficients (matrixRotation (V * cavityGroupRotation k e W)⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1)) u depth y) =
    cylinderCross (cavityPerturbationCoefficients (matrixRotation V⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1)) u depth x)
      (cavityPerturbationCoefficients (matrixRotation V⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1)) u depth y) := by
  simp only [cavityPerturbationCoefficients_cross, cavityWeightedKernel,
    cavityPerturbationKernel, cavityGroupRotation_overlap]

theorem cavityGroupRotation_gibbs_replica {N m depth r : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a))
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (F : (Fin r → Spin N × LabeledLeaf depth) → ℝ) :
    let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
    let I := cavitySpectralGroup (fun i => (e.symm i).1)
    let eig := diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1) I v t
    (∫ z, referenceReplicaMean ν (cavityRotationHamiltonian
      (matrixRotation (V * cavityGroupRotation k e W)⁻¹) eig I u z) F ∂gaussianCoordinates) =
      ∫ z, referenceReplicaMean ν (cavityRotationHamiltonian
        (matrixRotation V⁻¹) eig I u z) F ∂gaussianCoordinates := by
  intro ν I eig
  have h := cavity_replica_same_covariance ν
    (fun x => rotatedEnergy eig (matrixRotation V⁻¹) x.1)
    (cavityPerturbationCoefficients (matrixRotation (V * cavityGroupRotation k e W)⁻¹) I u depth)
    (cavityPerturbationCoefficients (matrixRotation V⁻¹) I u depth)
    (cavityGroupRotation_perturbation_covariance k e V W u) F
  have he (z : ℕ → ℝ) :
      cavityRotationHamiltonian (matrixRotation (V * cavityGroupRotation k e W)⁻¹) eig I u z =
        fun x : Spin N × LabeledLeaf depth => rotatedEnergy eig (matrixRotation V⁻¹) x.1 +
          cylinderField (cavityPerturbationCoefficients
            (matrixRotation (V * cavityGroupRotation k e W)⁻¹) I u depth x) z := by
    funext x
    dsimp only [cavityRotationHamiltonian, eig, I]
    rw [cavityGroupRotation_perturbed_energy k e V W lam v t]
  simp_rw [he]
  exact h

end InvariantIsing

end

end OAI

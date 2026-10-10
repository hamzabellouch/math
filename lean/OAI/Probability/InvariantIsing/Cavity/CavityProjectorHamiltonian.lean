import OAI.Probability.InvariantIsing.Cavity.CavityProjectorTensor

namespace OAI

/-! The actual base Gibbs law expressed using its labeled projectors.
This makes the law a measurable function of the data in the joint
projector/frame Haar factorization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityProjectorEnergy {N m : ℕ} (Q : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (c : Fin m → ℝ) (σ : Spin N) : ℝ :=
  (1/2 : ℝ) * ∑ a, c a * ((fun i => spinValue (σ i)) ⬝ᵥ
    (Q a *ᵥ (fun i => spinValue (σ i))))

lemma cavitySpectralProjector_form {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N))
    (x : Fin N → ℝ) :
    x ⬝ᵥ (cavitySpectralProjector V I *ᵥ x) =
      ∑ i ∈ I, ((V : Matrix (Fin N) (Fin N) ℝ).transpose *ᵥ x) i ^ 2 := by
  rw [cavitySpectralProjector, cavityConjugate, ← cavity_bilinear_conjugate]
  simp only [dotProduct, Matrix.mulVec_diagonal, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, pow_two]

lemma cavityProjectorEnergy_group {N m : ℕ} (g : Fin N → Fin m)
    (V : Orthogonal N) (c : Fin m → ℝ) (σ : Spin N) :
    cavityProjectorEnergy (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) c σ =
      rotatedEnergy (fun i => c (g i)) (matrixRotation V⁻¹) σ := by
  unfold cavityProjectorEnergy rotatedEnergy
  congr 1
  simp_rw [cavitySpectralProjector_form, cavitySpectralGroup, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

def cavityProjectorHamiltonian {N m depth : ℕ}
    (Q : Fin m → Matrix (Fin N) (Fin N) ℝ) (c : Fin m → ℝ)
    (u : ℕ → ℝ) (z : ℕ → ℝ) (x : Spin N × LabeledLeaf depth) : ℝ :=
  cavityProjectorEnergy Q c x.1 + cylinderField (cavityProjectorPerturbation Q u x) z

lemma cavityProjectorHamiltonian_energy {N m : ℕ} (g : Fin N → Fin m)
    (V : Orthogonal N) (lam v : Fin m → ℝ) (t : ℝ) (σ : Spin N) :
    cavityProjectorEnergy (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
      (fun a => t*lam a + 2*perturbationScale N*v a) σ =
    rotatedEnergy (diagonalPerturbedEigenvalues (fun i => lam (g i))
      (cavitySpectralGroup g) v t) (matrixRotation V⁻¹) σ := by
  rw [cavityProjectorEnergy_group]
  congr 1
  funext i
  simp [diagonalPerturbedEigenvalues, cavitySpectralGroup]

theorem cavity_projector_gibbs_replica {N m depth r : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (F : (Fin r → Spin N × LabeledLeaf depth) → ℝ) :
    let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
    (∫ z, referenceReplicaMean ν
      (cavityProjectorHamiltonian (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
        (fun a => t*lam a+2*perturbationScale N*v a) u z) F ∂gaussianCoordinates) =
    ∫ z, referenceReplicaMean ν (cavityRotationHamiltonian (matrixRotation V⁻¹)
      (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
      (cavitySpectralGroup g) u z) F ∂gaussianCoordinates := by
  intro ν
  let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t
  have he (z : ℕ → ℝ) :
      cavityProjectorHamiltonian (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
        (fun a => t*lam a+2*perturbationScale N*v a) u z =
      fun x : Spin N × LabeledLeaf depth => rotatedEnergy eig (matrixRotation V⁻¹) x.1 +
        cylinderField (cavityProjectorPerturbation
          (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) u x) z := by
    funext x
    unfold cavityProjectorHamiltonian
    rw [cavityProjectorHamiltonian_energy]
  simp_rw [he]
  exact cavity_replica_same_covariance ν
    (fun x => rotatedEnergy eig (matrixRotation V⁻¹) x.1)
    (cavityProjectorPerturbation (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) u)
    (cavityPerturbationCoefficients (matrixRotation V⁻¹) (cavitySpectralGroup g) u depth)
    (cavityProjectorPerturbation_cross V (cavitySpectralGroup g) u) F

end InvariantIsing

end

end OAI

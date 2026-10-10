import OAI.Probability.InvariantIsing.Cavity.CavityProjectorLog

namespace OAI

/-! The base logarithmic partition function in the same physical
projector variables as the capped cavity factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityProjectorLogPartition {N m depth : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (Q : Fin m → Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∫ z, Real.log (∫ x, Real.exp (cavityProjectorHamiltonian Q c u z x)
    ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    ∂gaussianCoordinates

lemma measurable_cavityProjectorLogPartition {Ω : Type*} [MeasurableSpace Ω]
    {N m depth : ℕ} (T : LabeledTree depth) (c : Fin m → ℝ) (u : ℕ → ℝ)
    (Q : Ω → Fin m → Matrix (Fin N) (Fin N) ℝ) (hQ : Measurable Q) :
    Measurable (fun ω => cavityProjectorLogPartition T c u (Q ω)) := by
  have hH := (measurable_cavityProjectorHamiltonian_pullback
    (N := N) (m := m) (depth := depth) Q hQ c u).exp
  exact hH.stronglyMeasurable.integral_prod_right'.measurable.log.stronglyMeasurable
    |>.integral_prod_right' |>.measurable

theorem cavity_projector_log_partition {N m depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ) :
    cavityProjectorLogPartition T (fun a => t*lam a+2*perturbationScale N*v a) u
      (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) =
    ∫ z, Real.log (∫ x, Real.exp
      (cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
        (cavitySpectralGroup g) u z x)
      ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      ∂gaussianCoordinates := by
  let H := fun x : Spin N × LabeledLeaf depth =>
    rotatedEnergy (diagonalPerturbedEigenvalues (fun i => lam (g i))
      (cavitySpectralGroup g) v t) (matrixRotation V⁻¹) x.1
  let A := fun x : Spin N × LabeledLeaf depth =>
    cavityProjectorPerturbation (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) u x
  let C := fun x : Spin N × LabeledLeaf depth =>
    cavityPerturbationCoefficients (matrixRotation V⁻¹) (cavitySpectralGroup g) u depth x
  have he z : (fun x : Spin N × LabeledLeaf depth => cavityProjectorHamiltonian
      (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
      (fun a => t*lam a+2*perturbationScale N*v a) u z x) =
      fun x => H x+cylinderField (A x) z := by
    funext x
    unfold cavityProjectorHamiltonian
    rw [cavityProjectorHamiltonian_energy]
  unfold cavityProjectorLogPartition
  simp_rw [he]
  exact cavity_log_partition_same_covariance _ H A C
    (fun x y => cavityProjectorPerturbation_cross V (cavitySpectralGroup g) u x y)

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Cavity.CavityProjectorCavity
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorGibbsHaar

namespace OAI

/-! The projector realization identifies the full normalized cavity
cutoff law, including its extra finite spins and added potential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_projector_extra_cutoff {N n m depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (W : (Spin N × LabeledLeaf depth) × Spin n → ℝ)
    (s : Set ((Spin N × LabeledLeaf depth) × Spin n))
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    let ν : Measure ((Spin N × LabeledLeaf depth) × Spin n) := (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
      (uniformSpinPrior n)
    (∫ z, cavityCutoffReplicaMean ν
      (fun x => cavityProjectorHamiltonian
        (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
        (fun a => t*lam a+2*perturbationScale N*v a) u z x.1 + W x) s F
      ∂gaussianCoordinates) =
    ∫ z, cavityCutoffReplicaMean ν
      (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
        (cavitySpectralGroup g) u z x.1 + W x) s F ∂gaussianCoordinates := by
  intro ν
  let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t
  let H := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    rotatedEnergy eig (matrixRotation V⁻¹) x.1.1 + W x
  let A := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    cavityProjectorPerturbation (fun a => cavitySpectralProjector V (cavitySpectralGroup g a)) u x.1
  let C := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    cavityPerturbationCoefficients (matrixRotation V⁻¹) (cavitySpectralGroup g) u depth x.1
  have he z : (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      cavityProjectorHamiltonian (fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
        (fun a => t*lam a+2*perturbationScale N*v a) u z x.1 + W x) =
      fun x => H x+cylinderField (A x) z := by
    funext x
    unfold cavityProjectorHamiltonian
    rw [cavityProjectorHamiltonian_energy]
    dsimp only [H, A, eig]
    ring
  have hc z : (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      cavityRotationHamiltonian (matrixRotation V⁻¹) eig (cavitySpectralGroup g) u z x.1 + W x) =
      fun x => H x+cylinderField (C x) z := by
    funext x
    dsimp only [cavityRotationHamiltonian, H, C]
    ring
  calc
    _ = ∫ z, cavityCutoffReplicaMean ν (fun x => H x+cylinderField (A x) z) s F
        ∂gaussianCoordinates := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => congrArg (fun J => cavityCutoffReplicaMean ν J s F) (he z)
    _ = ∫ z, cavityCutoffReplicaMean ν (fun x => H x+cylinderField (C x) z) s F
        ∂gaussianCoordinates := cavity_cutoff_same_covariance ν H A C
      (fun x y => cavityProjectorPerturbation_cross V (cavitySpectralGroup g) u x.1 y.1) s F
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => congrArg (fun J => cavityCutoffReplicaMean ν J s F) (hc z).symm

theorem cavity_projector_cavity_cutoff {N n m d depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ) (A : CavityFactorBlocks d n)
    (p : CavityProjectorFrame N m d)
    (hp : p.1 = fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    cavityProjectorCavityMean (N := N) (n := n) (m := m) (d := d) (depth := depth)
      T (fun a => t*lam a+2*perturbationScale N*v a) u t D A F p =
    ∫ z, cavityCutoffReplicaMean
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n))
      (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun j => lam (g j)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z x.1 +
        t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2)
      {x | 1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D} F ∂gaussianCoordinates := by
  unfold cavityProjectorCavityMean
  rw [hp]
  exact cavity_projector_extra_cutoff (N := N) (n := n) (m := m) (depth := depth)
    g V T lam v u t _ _ F

end InvariantIsing

end

end OAI

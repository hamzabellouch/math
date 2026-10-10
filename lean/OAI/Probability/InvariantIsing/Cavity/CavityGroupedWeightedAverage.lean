import OAI.Probability.InvariantIsing.Cavity.CavityGroupedCutoffAverage
import OAI.Probability.InvariantIsing.Cavity.CavityRotationCutoffWeight

namespace OAI

/-! Fresh-frame cutoff tests over the actual base Gibbs probability.
The diagonal and Gaussian perturbations stay in that base law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_grouped_weighted_average {N n m q d depth : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (k a))) [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t D : ℝ)
    (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    (∫ V, cavityProjectorCavityMean T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D B F
      (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
        (V : Matrix (Fin N) (Fin N) ℝ)*cavityGroupedSelectedFrame k e f A) ∂μ) =
    ∫ V, ∫ W, ∫ z, cavityWeightedReplicaMean
      (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
        (cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
            (cavitySpectralGroup (fun i => (e.symm i).1)) v t)
          (cavitySpectralGroup (fun i => (e.symm i).1)) u z)).prod (uniformSpinPrior n))
      ({x | 1+‖cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
        (cavityGroupHaarFrames A W) x.1.1‖^2 ≤ D}.indicator (fun x =>
          Real.exp (t*cavityLogFactor B.1 B.2.1 B.2.2
            (cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
              (cavityGroupHaarFrames A W) x.1.1) x.2))) F ∂gaussianCoordinates ∂η ∂μ := by
  rw [cavity_grouped_cutoff_average k e f A μ η T lam v u t D B F hM hF]
  apply integral_congr_ae
  apply ae_of_all
  intro V
  apply integral_congr_ae
  apply ae_of_all
  intro W
  exact cavity_rotation_cutoff_weight (matrixRotation V⁻¹) T
    (diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
      (cavitySpectralGroup (fun i => (e.symm i).1)) v t)
    (cavitySpectralGroup (fun i => (e.symm i).1)) u hu
    (fun x => t*cavityLogFactor B.1 B.2.1 B.2.2
      (cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
        (cavityGroupHaarFrames A W) x.1) x.2) _ F

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalGroupAverage
import OAI.Probability.InvariantIsing.Magnetic.RestrictedCanonicalWeighted

namespace OAI

/-! The original full-system cutoff and its actual fresh-group Gibbs
representation have the same limit after deterministic coefficient replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Matrix Topology

namespace InvariantIsing

def restrictedCanonicalGroupCutoffMean {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N))
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a)))
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t D : ℝ) (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) : ℝ :=
  let E := cavityBaseGroupEquiv k e g
  let A := cavityCanonicalGroupFrame k e g hk
  ∫ V, ∫ W, ∫ z, cavityWeightedReplicaMean
    (((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).tilted
      (cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
          (cavitySpectralGroup (fun i => (E.symm i).1)) v t)
        (cavitySpectralGroup (fun i => (E.symm i).1)) u z)).prod (restrictedSpinPrior Cset hCset))
    ({x | 1+‖cavitySelectedSiteProjection (fun j => (g j,j))
      (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
      (cavityGroupHaarFrames A W) x.1.1‖^2 ≤ D}.indicator (fun x =>
        Real.exp (t*cavityLogFactor B.1 B.2.1 B.2.2
          (cavitySelectedSiteProjection (fun j => (g j,j))
            (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
            (cavityGroupHaarFrames A W) x.1.1) x.2))) F ∂gaussianCoordinates ∂η ∂μ

end InvariantIsing

end

end OAI

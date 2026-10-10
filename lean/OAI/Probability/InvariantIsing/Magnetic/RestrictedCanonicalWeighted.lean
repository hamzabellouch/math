import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalGroupAverage
import OAI.Probability.InvariantIsing.Magnetic.RestrictedGroupedWeighted

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix
namespace InvariantIsing

theorem restricted_canonical_weighted_average {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a)))
    [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t D : ℝ) (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    (∫ V, restrictedProjectorCavityMean S hS Cset hCset T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D B F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e g)) ∂μ) =
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
              (cavityGroupHaarFrames A W) x.1.1) x.2))) F ∂gaussianCoordinates ∂η ∂μ := by
  simp_rw [cavityCanonicalProjectorFrame_grouped k e g hk]
  exact restricted_grouped_weighted_average S hS Cset hCset (cavityBaseGroupDimension k g)
    (cavityBaseGroupEquiv k e g) (fun j => (g j,j)) (cavityCanonicalGroupFrame k e g hk)
    μ η T lam v u hu t D B F hM hF

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Cavity.CavityGroupedCappedLog
import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalGroupAverage

namespace OAI

/-! The canonical base-projector logarithm is the actual fresh-group
spin/leaf logarithm, including its geometric quadratic penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_canonical_capped_log_group_average {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))
    [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t cap δ : ℝ) (hcap : 0 ≤ cap)
    (B : CavityFactorBlocks d n) :
    (∫ V, cavityProjectorCappedLog T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ B (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂μ) =
    let dims := cavityBaseGroupDimension k a₀
    let E := cavityBaseGroupEquiv k e a₀
    let A₀ := cavityCanonicalGroupFrame k e a₀ hk
    ∫ V, ∫ W, ∫ z, Real.log (∫ x, Real.exp
      (min (t*cavityLogFactor B.1 B.2.1 B.2.2
        (cavitySelectedSiteProjection (fun j => (a₀ j,j)) (cavityGroupSpinCoordinates dims E V)
          (cavityGroupHaarFrames A₀ W) x.1.1) x.2) cap -
        δ*(1+‖cavitySelectedSiteProjection (fun j => (a₀ j,j)) (cavityGroupSpinCoordinates dims E V)
          (cavityGroupHaarFrames A₀ W) x.1.1‖^2))
      ∂((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n)).tilted (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
            (cavitySpectralGroup (fun i => (E.symm i).1)) v t)
          (cavitySpectralGroup (fun i => (E.symm i).1)) u z x.1))
        ∂gaussianCoordinates ∂η ∂μ := by
  dsimp only
  simp_rw [cavityCanonicalProjectorFrame_grouped k e a₀ hk]
  apply cavity_grouped_capped_log_average _ _ _ _ ?_ μ η T lam v u hu t cap δ hcap B
  rw [cavityCanonicalGroupFrame_special, cavityCanonicalSpecial_gram]

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Cavity.CavityOrbitAverage
import OAI.Probability.InvariantIsing.Cavity.CavityGroupedCoordinates
import OAI.Probability.InvariantIsing.Cavity.CavityFrameLogBound

namespace OAI

/-! Fresh group rotations inside the actual capped logarithm.  The
base Gaussian Hamiltonian and its original Gibbs normalization are
preserved by the labeled-projector stabilizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_grouped_capped_log_average {N n m q d depth : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (hA : (cavityGroupedSelectedFrame k e f A).transpose*cavityGroupedSelectedFrame k e f A=1)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (k a))) [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t cap δ : ℝ) (hcap : 0 ≤ cap)
    (B : CavityFactorBlocks d n) :
    (∫ V, cavityProjectorCappedLog T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ B
      (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
        (V : Matrix (Fin N) (Fin N) ℝ)*cavityGroupedSelectedFrame k e f A) ∂μ) =
    ∫ V, ∫ W, ∫ z, Real.log (∫ x, Real.exp
      (min (t*cavityLogFactor B.1 B.2.1 B.2.2
        (cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
          (cavityGroupHaarFrames A W) x.1.1) x.2) cap -
        δ*(1+‖cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
          (cavityGroupHaarFrames A W) x.1.1‖^2))
      ∂((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n)).tilted (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
            (cavitySpectralGroup (fun i => (e.symm i).1)) v t)
          (cavitySpectralGroup (fun i => (e.symm i).1)) u z x.1))
        ∂gaussianCoordinates ∂η ∂μ := by
  let c := fun a => t*lam a+2*perturbationScale N*v a
  let S := cavityGroupedSelectedFrame k e f A
  let G : CavityProjectorFrame N m d → ℝ := cavityProjectorCappedLog T c u t cap δ B
  have hG : Measurable G := measurable_cavityProjectorCappedLog T c u t cap δ
    (fun _ => B) measurable_const id measurable_id
  have hb (V : Orthogonal N) : ‖G
      (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
        (V : Matrix (Fin N) (Fin N) ℝ)*S)‖ ≤
      (|t| *cavityFactorSize B.1 B.2.1 B.2.2+|δ|)*(1+N) := by
    rw [Real.norm_eq_abs]
    exact cavity_projector_capped_log_bound (fun i => (e.symm i).1) V T lam v u hu
      t cap δ hcap B le_rfl _ rfl (cavity_orthogonal_frame_gram V S hA)
  rw [cavity_labeled_stabilizer_average_on_orbit k e S μ η G hG _ hb]
  apply integral_congr_ae
  apply ae_of_all
  intro V
  apply integral_congr_ae
  apply ae_of_all
  intro W
  let p : CavityProjectorFrame N m d :=
    (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*
        ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*S))
  change cavityProjectorCappedLog T c u t cap δ B p = _
  rw [cavity_projector_capped_log (fun i => (e.symm i).1) V T lam v u t cap δ B p rfl]
  simp only [p, S, cavityGroupedSelectedFrame_rotated_coordinates]

end InvariantIsing

end

end OAI

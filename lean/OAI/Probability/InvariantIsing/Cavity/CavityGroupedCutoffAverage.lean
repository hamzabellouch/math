import OAI.Probability.InvariantIsing.Cavity.CavityGroupedCoordinates

namespace OAI

/-! The fixed-block Haar cutoff is precisely the fresh-group-frame
observable over the original base Hamiltonian. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_grouped_cutoff_average {N n m q d depth : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (k a))) [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ)
    (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    (∫ V, cavityProjectorCavityMean T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D B F
      (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
        (V : Matrix (Fin N) (Fin N) ℝ)*cavityGroupedSelectedFrame k e f A) ∂μ) =
    ∫ V, ∫ W, ∫ z, cavityCutoffReplicaMean
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n))
      (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1)
          (cavitySpectralGroup (fun i => (e.symm i).1)) v t)
        (cavitySpectralGroup (fun i => (e.symm i).1)) u z x.1 +
        t*cavityLogFactor B.1 B.2.1 B.2.2
          (cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
            (cavityGroupHaarFrames A W) x.1.1) x.2)
      {x | 1+‖cavitySelectedSiteProjection f (cavityGroupSpinCoordinates k e V)
        (cavityGroupHaarFrames A W) x.1.1‖^2 ≤ D} F ∂gaussianCoordinates ∂η ∂μ := by
  let c := fun a => t*lam a+2*perturbationScale N*v a
  let G : CavityProjectorFrame N m d → ℝ := cavityProjectorCavityMean T c u t D B F
  have hFs : Measurable (fun x : CavityProjectorFrame N m d ×
      (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) => F x.2) :=
    (measurable_of_countable F).comp measurable_snd
  have hG : Measurable G := measurable_cavityProjectorCavityMean T c u t D
    (fun _ => B) measurable_const id measurable_id (fun _ => F) hFs
  have hb : ∀ p, ‖G p‖ ≤ M := fun p => cavityProjectorCavityMean_bound T c u t D B F hM hF p
  rw [cavity_labeled_stabilizer_average k e (cavityGroupedSelectedFrame k e f A) μ η G hG M hb]
  apply integral_congr_ae
  apply ae_of_all
  intro V
  apply integral_congr_ae
  apply ae_of_all
  intro W
  let p : CavityProjectorFrame N m d :=
    (fun a => cavitySpectralProjector V (cavitySpectralGroup (fun i => (e.symm i).1) a),
      (V : Matrix (Fin N) (Fin N) ℝ)*
        ((cavityGroupRotation k e W : Matrix (Fin N) (Fin N) ℝ)*
          cavityGroupedSelectedFrame k e f A))
  have hp : p.1 = fun a => cavitySpectralProjector V
    (cavitySpectralGroup (fun i => (e.symm i).1) a) := rfl
  change cavityProjectorCavityMean T c u t D B F p = _
  rw [cavity_projector_cavity_cutoff (fun i => (e.symm i).1) V T lam v u t D B p hp F]
  simp only [p, cavityGroupedSelectedFrame_rotated_coordinates]

end InvariantIsing

end

end OAI

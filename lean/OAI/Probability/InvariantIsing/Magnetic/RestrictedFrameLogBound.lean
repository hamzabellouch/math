import OAI.Probability.InvariantIsing.Magnetic.RestrictedProjectorLog
import OAI.Probability.InvariantIsing.Cavity.CavityFrameLogBound

namespace OAI

/-! Finite bounds for the constrained cavity logarithm on orthonormal frames. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem restricted_projector_capped_log_bound {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (R : Finset (Spin n)) (hR : R.Nonempty)
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (A : CavityFactorBlocks d n) {D : ℝ}
    (hA : cavityFactorSize A.1 A.2.1 A.2.2 ≤ D)
    (p : CavityProjectorFrame N m d)
    (hp : p.1=fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
    (hFrame : p.2.transpose*p.2=1) :
    |restrictedProjectorCappedLog S hS R hR T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ A p| ≤ (|t| *D+|δ|)*(1+N) := by
  rw [restricted_projector_capped_log S hS R hR g V T lam v u t cap δ A p hp]
  let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t
  let X := (Spin N × LabeledLeaf depth) × Spin n
  let ν : Measure X := (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).prod
    (restrictedSpinPrior R hR : Measure (Spin n))
  let H : X → ℝ := fun x => rotatedEnergy eig (matrixRotation V⁻¹) x.1.1
  let C : X → ℕ →₀ ℝ := fun x => cavityPerturbationCoefficients (matrixRotation V⁻¹)
    (cavitySpectralGroup g) u depth x.1
  let W : X → ℝ := fun x =>
    min (t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
      δ*(1+‖cavityFrameCoordinates p.2 x.1.1‖^2)
  have hH (x : X) : |H x| ≤ ∑ σ : Spin N, |rotatedEnergy eig (matrixRotation V⁻¹) σ| :=
    Finset.single_le_sum (f := fun σ : Spin N => |rotatedEnergy eig (matrixRotation V⁻¹) σ|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ x.1.1)
  have hC (x : X) : (C x).sum (fun _ c => c^2) ≤ 4*(N*perturbationScale N^2) :=
    cavityPerturbationCoefficients_sq_le (matrixRotation V⁻¹) (cavitySpectralGroup g) u hu x.1
  have hW (x : X) : |W x| ≤ (|t| *D+|δ|)*(1+N) :=
    cavity_frame_capped_potential_bound p.2 hFrame A hA t cap δ hcap x.1.1 x.2
  exact cavity_bounded_log_weight_mean_bound ν H hH C hC W hW

end InvariantIsing

end

end OAI

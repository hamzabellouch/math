import OAI.Probability.InvariantIsing.Cavity.CavityProjectorLog
import OAI.Probability.InvariantIsing.Cavity.CavityLogMeanBound
import OAI.Probability.InvariantIsing.Cavity.CavityProjectionControl
import OAI.Probability.InvariantIsing.Cavity.CavityVanishingPenalty

namespace OAI

/-! Finite-volume bounds for the capped logarithm on the canonical
orthonormal frame.  These bounds are only used for Haar integrability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma cavityCanonicalSpecial_gram {N d : ℕ} {ι : Type*}
    (e : (ι ⊕ Fin d) ≃ Fin N) :
    (cavityCanonicalSpecial e).transpose * cavityCanonicalSpecial e = 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply, cavityCanonicalSpecial, Matrix.one_apply, eq_comm]

lemma cavity_orthogonal_frame_gram {N d : ℕ} (V : Orthogonal N)
    (S : Matrix (Fin N) (Fin d) ℝ) (hS : S.transpose*S=1) :
    ((V : Matrix (Fin N) (Fin N) ℝ)*S).transpose *
      ((V : Matrix (Fin N) (Fin N) ℝ)*S)=1 := by
  have hV := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp V.property
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc
    (V : Matrix (Fin N) (Fin N) ℝ).transpose, hV, Matrix.one_mul, hS]

lemma cavity_canonical_action_frame_gram {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (V : Orthogonal N) :
    let S := (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)).2
    S.transpose * S = 1 := by
  intro S
  have hV := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp V.property
  change ((V : Matrix (Fin N) (Fin N) ℝ)*cavityCanonicalSpecial e).transpose *
    ((V : Matrix (Fin N) (Fin N) ℝ)*cavityCanonicalSpecial e) = 1
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc
    (V : Matrix (Fin N) (Fin N) ℝ).transpose, hV, Matrix.one_mul,
    cavityCanonicalSpecial_gram]

lemma cavity_frame_coordinates_norm_le {N d : ℕ} (S : Matrix (Fin N) (Fin d) ℝ)
    (hS : S.transpose*S=1) (σ : Spin N) : ‖cavityFrameCoordinates S σ‖^2 ≤ N := by
  have h := cavity_frame_transpose_contraction S hS (spinVector σ)
  rw [spinVector_norm_sq] at h
  exact h

lemma cavity_frame_capped_potential_bound {N n d : ℕ}
    (S : Matrix (Fin N) (Fin d) ℝ) (hS : S.transpose*S=1)
    (A : CavityFactorBlocks d n) {D : ℝ}
    (hA : cavityFactorSize A.1 A.2.1 A.2.2 ≤ D)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (σ : Spin N) (ε : Spin n) :
    |min (t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates S σ) ε) cap -
      δ*(1+‖cavityFrameCoordinates S σ‖^2)| ≤ (|t| *D+|δ|)*(1+N) := by
  have hD := (cavityFactorSize_nonneg A.1 A.2.1 A.2.2).trans hA
  have hy := cavity_frame_coordinates_norm_le S hS σ
  have hg := cavity_logFactor_growth A.1 A.2.1 A.2.2 (cavityFrameCoordinates S σ) ε
  have hg' : |cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates S σ) ε| ≤ D*(1+N) :=
    hg.trans (mul_le_mul hA (add_le_add (le_refl 1) hy)
      (by positivity) hD)
  have hm := cavity_abs_min_cap (h := t*cavityLogFactor A.1 A.2.1 A.2.2
    (cavityFrameCoordinates S σ) ε) hcap
  calc
    _ ≤ |min (t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates S σ) ε) cap| +
        |δ*(1+‖cavityFrameCoordinates S σ‖^2)| := abs_sub _ _
    _ ≤ |t| *(D*(1+N))+|δ| *(1+N) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1+‖cavityFrameCoordinates S σ‖^2)]
      exact add_le_add (hm.trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hg' (abs_nonneg t)))
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hy) (abs_nonneg δ))
    _ = _ := by ring

theorem cavity_projector_capped_log_bound {N n m d depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (A : CavityFactorBlocks d n) {D : ℝ}
    (hA : cavityFactorSize A.1 A.2.1 A.2.2 ≤ D)
    (p : CavityProjectorFrame N m d)
    (hp : p.1=fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
    (hS : p.2.transpose*p.2=1) :
    |cavityProjectorCappedLog T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ A p| ≤ (|t| *D+|δ|)*(1+N) := by
  rw [cavity_projector_capped_log g V T lam v u t cap δ A p hp]
  let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t
  let X := (Spin N × LabeledLeaf depth) × Spin n
  let ν : Measure X := (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
    (uniformSpinPrior n : Measure (Spin n))
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
    cavity_frame_capped_potential_bound p.2 hS A hA t cap δ hcap x.1.1 x.2
  exact cavity_bounded_log_weight_mean_bound ν H hH C hC W hW

end InvariantIsing

end

end OAI

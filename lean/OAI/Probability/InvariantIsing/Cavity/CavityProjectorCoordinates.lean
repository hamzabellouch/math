import OAI.Probability.InvariantIsing.Cavity.CavityLabeledProjectors
import OAI.Probability.InvariantIsing.Cavity.CavityGroupOverlapInvariant

namespace OAI

/-! Projector coordinates give the same Gaussian covariance as the
eigenbasis coordinates, without choosing an eigenbasis measurably. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavitySpectralProjector {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ :=
  cavityConjugate V (Matrix.diagonal (fun i => if i∈I then (1:ℝ) else 0))

lemma cavitySpectralProjector_transpose {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N)) :
    (cavitySpectralProjector V I).transpose = cavitySpectralProjector V I := by
  simp only [cavitySpectralProjector, cavityConjugate, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]

lemma cavitySpectralProjector_square {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N)) :
    cavitySpectralProjector V I * cavitySpectralProjector V I = cavitySpectralProjector V I := by
  let D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal (fun i => if i∈I then (1:ℝ) else 0)
  have hV := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp V.property
  have hD : D*D=D := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> norm_num
  change ((V : Matrix (Fin N) (Fin N) ℝ)*D*(V : Matrix (Fin N) (Fin N) ℝ).transpose)*
    ((V : Matrix (Fin N) (Fin N) ℝ)*D*(V : Matrix (Fin N) (Fin N) ℝ).transpose) = _
  calc
    _ = (V : Matrix (Fin N) (Fin N) ℝ)*D*
        ((V : Matrix (Fin N) (Fin N) ℝ).transpose*(V : Matrix (Fin N) (Fin N) ℝ))*D*
        (V : Matrix (Fin N) (Fin N) ℝ).transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc _ D D, hD]; rfl

lemma cavity_projector_coordinate_dot {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N))
    (x y : Fin N → ℝ) :
    (cavitySpectralProjector V I *ᵥ x) ⬝ᵥ (cavitySpectralProjector V I *ᵥ y) =
      x ⬝ᵥ (cavitySpectralProjector V I *ᵥ y) := by
  calc
    _ = x ⬝ᵥ (cavitySpectralProjector V I *ᵥ (cavitySpectralProjector V I *ᵥ y)) := by
      rw [Matrix.dotProduct_mulVec x, ← Matrix.mulVec_transpose, cavitySpectralProjector_transpose]
    _ = _ := by rw [Matrix.mulVec_mulVec, cavitySpectralProjector_square]

def cavityProjectorSpinCoordinate {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (σ : Spin N) (i : Fin N) : ℝ := (P *ᵥ (fun j => spinValue (σ j))) i / Real.sqrt (N:ℝ)

theorem cavity_projector_coordinate_covariance {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N))
    (σ τ : Spin N) :
    (∑ i, cavityProjectorSpinCoordinate (cavitySpectralProjector V I) σ i *
      cavityProjectorSpinCoordinate (cavitySpectralProjector V I) τ i) =
      projectedOverlap (matrixRotation V⁻¹) I σ τ := by
  simp only [cavityProjectorSpinCoordinate, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N), ← Finset.sum_div]
  rw [div_eq_mul_inv, mul_comm, projectedOverlap_conjugate]
  congr 1
  exact cavity_projector_coordinate_dot V I _ _

end InvariantIsing

end

end OAI

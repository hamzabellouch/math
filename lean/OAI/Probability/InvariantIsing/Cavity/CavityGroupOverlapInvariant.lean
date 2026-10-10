import OAI.Probability.InvariantIsing.Cavity.CavitySpectralStabilizer
import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticCompression
import OAI.Probability.InvariantIsing.Cavity.CavityProjectionGeometry

namespace OAI

/-! Exact preservation of each projected overlap under the independent
rotations inside the base spectral groups. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_bilinear_conjugate {N : ℕ} (V A : Matrix (Fin N) (Fin N) ℝ)
    (x y : Fin N → ℝ) :
    (V.transpose *ᵥ x) ⬝ᵥ (A *ᵥ (V.transpose *ᵥ y)) =
      x ⬝ᵥ ((V * A * V.transpose) *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec x V, ← Matrix.mulVec_transpose]

lemma projectedOverlap_conjugate {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N))
    (σ τ : Spin N) :
    projectedOverlap (matrixRotation V⁻¹) I σ τ = (N : ℝ)⁻¹ *
      ((fun i => spinValue (σ i)) ⬝ᵥ
        (cavityConjugate V (Matrix.diagonal (fun i => if i ∈ I then (1 : ℝ) else 0)) *ᵥ
          (fun i => spinValue (τ i)))) := by
  rw [cavityConjugate, ← cavity_bilinear_conjugate]
  change (N : ℝ)⁻¹ * (∑ i ∈ I, _ * _) = (N : ℝ)⁻¹ *
    (((V : Matrix (Fin N) (Fin N) ℝ).transpose *ᵥ (fun i => spinValue (σ i))) ⬝ᵥ
      (Matrix.diagonal (fun i => if i ∈ I then (1 : ℝ) else 0) *ᵥ
        ((V : Matrix (Fin N) (Fin N) ℝ).transpose *ᵥ (fun i => spinValue (τ i)))))
  simp only [dotProduct, Matrix.mulVec_diagonal, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  rfl

theorem cavityGroupRotation_overlap {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a))
    (a : Fin m) (σ τ : Spin N) :
    projectedOverlap (matrixRotation (V * cavityGroupRotation k e W)⁻¹)
      (cavitySpectralGroup (fun i => (e.symm i).1) a) σ τ =
      projectedOverlap (matrixRotation V⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1) a) σ τ := by
  rw [projectedOverlap_conjugate, projectedOverlap_conjugate, cavityConjugate_mul]
  have hmask : (Matrix.diagonal (fun i : Fin N =>
      if i ∈ cavitySpectralGroup (fun i => (e.symm i).1) a then (1 : ℝ) else 0)) =
      Matrix.diagonal (fun i => (fun b => if b = a then (1 : ℝ) else 0) (e.symm i).1) := by
    congr 1
    funext i
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hmask]
  rw [cavityGroupRotation_conjugate k e W (fun b => if b = a then (1 : ℝ) else 0)]

theorem cavityGroupRotation_energy {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (W : (a : Fin m) → Orthogonal (k a))
    (lam : Fin m → ℝ) (σ : Spin N) :
    rotatedEnergy (fun i => lam (e.symm i).1)
      (matrixRotation (V * cavityGroupRotation k e W)⁻¹) σ =
      rotatedEnergy (fun i => lam (e.symm i).1) (matrixRotation V⁻¹) σ := by
  rw [← cavityQuadratic_inverse_rotation, ← cavityQuadratic_inverse_rotation]
  change cavityQuadratic (cavityConjugate (V * cavityGroupRotation k e W)
    (Matrix.diagonal (fun i => lam (e.symm i).1))) _ = _
  rw [cavityConjugate_mul, cavityGroupRotation_conjugate]
  rfl

end InvariantIsing

end

end OAI

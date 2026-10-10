import OAI.Geometry.NodalSets.Charts.TangentialMatrixInverse

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
local instance : DecidableEq (Fin 1) := fun a b ↦ decidableEq_of_subsingleton a b
local instance : Fintype (Fin 1) := Unique.fintype

def radialVolumeMatrix (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ) (x : Fin 5 → ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  weightedBaseMatrix A rho + replicateCol (Fin 1) ((1-rho) • x) * replicateRow (Fin 1) x

lemma radialVolumeMatrix_tangent (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ)
    (x v : Fin 5 → ℝ) (hv : x ⬝ᵥ v = 0) :
    radialVolumeMatrix A rho x *ᵥ v = weightedBaseMatrix A rho *ᵥ v := by
  rw [radialVolumeMatrix,add_mulVec,← mulVec_mulVec,replicateRow_mulVec_eq_const,hv]
  simp

lemma radialVolumeMatrix_radial (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (rho : ℝ) (x : Fin 5 → ℝ) (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) :
    radialVolumeMatrix A rho x *ᵥ x = x := by
  simp only [radialVolumeMatrix,add_mulVec,weightedBaseMatrix,smul_mulVec,
    radial_fixed_inverse A hA x hx,← mulVec_mulVec,replicateRow_mulVec_eq_const,hn]
  ext i
  simp [mulVec,dotProduct]
  ring

lemma radialVolumeMatrix_det (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (x : Fin 5 → ℝ)
    (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) :
    (radialVolumeMatrix A rho x).det = rho^4 / A.det := by
  have hh := weightedBaseMatrix_posDef hA hr
  rw [radialVolumeMatrix,det_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (isUnit_iff_ne_zero.mpr hh.det_pos.ne'),weightedBaseMatrix_inverse hA hr]
  rw [Matrix.mul_assoc,← replicateCol_mulVec,smul_mulVec,mulVec_smul,hx,
    replicateRow_mul_replicateCol]
  conv_lhs => arg 2; rw [det_unique]

  simp only [Matrix.add_apply,Matrix.one_apply_eq,Matrix.of_apply,
    dotProduct_smul,hn,smul_eq_mul,mul_one]
  rw [weightedBaseMatrix,Matrix.det_smul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
  simp only [Fintype.card_fin]
  field_simp
  ring

end
end Yau.Geometry

end OAI

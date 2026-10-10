import OAI.Geometry.NodalSets.Elliptic.IndependentWeightedMatrix

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma symmetric_dot_mulVec (A : Matrix n n ℝ) (hA : A.IsHermitian) (x v : n → ℝ) :
    x ⬝ᵥ (A *ᵥ v) = (A *ᵥ x) ⬝ᵥ v := by
  simp only [dotProduct,mulVec,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := hA.apply i j
  simp only [star_trivial] at h
  rw [h]
  ring

lemma radial_fixed_inverse (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : n → ℝ) (hx : A *ᵥ x = x) : A⁻¹ *ᵥ x = x := by
  calc
    A⁻¹ *ᵥ x = A⁻¹ *ᵥ (A *ᵥ x) := congrArg (fun v ↦ A⁻¹ *ᵥ v) hx.symm
    _ = x := by
      rw [mulVec_mulVec,A.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),one_mulVec]

omit [DecidableEq n] in
lemma radial_orthogonal_preserved (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (x v : n → ℝ) (hx : A *ᵥ x = x) (hv : x ⬝ᵥ v = 0) :
    x ⬝ᵥ (A *ᵥ v) = 0 := by
  rw [symmetric_dot_mulVec A hA,hx,hv]

lemma inverse_radial_orthogonal_preserved (A : Matrix n n ℝ) (hA : A.PosDef)
    (x v : n → ℝ) (hx : A *ᵥ x = x) (hv : x ⬝ᵥ v = 0) :
    x ⬝ᵥ (A⁻¹ *ᵥ v) = 0 :=
  radial_orthogonal_preserved A⁻¹ hA.inv.1 x v (radial_fixed_inverse A hA x hx) hv

lemma weighted_tangent_inverse (A : Matrix n n ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (v : n → ℝ) :
    (rho⁻¹ • A) *ᵥ (weightedBaseMatrix A rho *ᵥ v) = v ∧
      weightedBaseMatrix A rho *ᵥ ((rho⁻¹ • A) *ᵥ v) = v := by
  have hh := weightedBaseMatrix_posDef hA hr
  rw [← weightedBaseMatrix_inverse hA hr]
  constructor
  · rw [mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hh.det_pos.ne'),one_mulVec]
  · rw [mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hh.det_pos.ne'),one_mulVec]

end
end Yau.Geometry

end OAI

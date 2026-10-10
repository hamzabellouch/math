import Mathlib.Algebra.Order.Star.Real
import OAI.Geometry.NodalSets.Charts.WeightedCircleMatrix

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

def weightedBaseMatrix (A : Matrix n n ℝ) (rho : ℝ) : Matrix n n ℝ := rho • A⁻¹

lemma weightedBaseMatrix_posDef {A : Matrix n n ℝ} (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) : (weightedBaseMatrix A rho).PosDef := hA.inv.smul hr

lemma weightedBaseMatrix_inverse {A : Matrix n n ℝ} (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) : (weightedBaseMatrix A rho)⁻¹ = rho⁻¹ • A := by
  let : Invertible rho := invertibleOfNonzero hr.ne'
  rw [weightedBaseMatrix,Matrix.inv_smul A⁻¹ rho (isUnit_iff_ne_zero.mpr hA.inv.det_pos.ne'),
    invOf_eq_inv,Matrix.nonsing_inv_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')]

lemma independent_weighted_lift {A : Matrix n n ℝ} (hA : A.PosDef)
    {rho gamma0 : ℝ} (hr : 0 < rho) (hg : 0 < gamma0) :
    let G := weightedCircleMatrix (weightedBaseMatrix A rho) rho gamma0
    G.PosDef ∧ Real.sqrt G.det = rho*gamma0 ∧
      ∀ i j, G⁻¹ (Sum.inl i) (Sum.inl j) = rho⁻¹*A i j := by
  have hh := weightedBaseMatrix_posDef hA hr
  refine ⟨weightedCircleMatrix_posDef hh hr hg,weightedCircleMatrix_volume hh hr hg,?_⟩
  intro i j
  rw [weightedCircleMatrix_horizontal_inverse hh hr hg,weightedBaseMatrix_inverse hA hr]
  rfl

end
end Yau.Geometry

end OAI

import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! Positive affine rescalings of the plane and their exact area factor. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def planarAffineHomeomorph (a : EuclideanPlane) (s : ℝ) (hs : s ≠ 0) :
    EuclideanPlane ≃ₜ EuclideanPlane where
  toFun x := a+s • x
  invFun y := s⁻¹ • (y-a)
  left_inv x := by simp [smul_smul, hs]
  right_inv y := by simp [smul_smul, hs]
  continuous_toFun := continuous_const.add (continuous_id.const_smul s)
  continuous_invFun := (continuous_id.sub continuous_const).const_smul s⁻¹

lemma planarAffineHomeomorph_apply (a : EuclideanPlane) (s : ℝ) (hs : s ≠ 0) (x : EuclideanPlane) :
    planarAffineHomeomorph a s hs x = a+s • x := rfl

lemma planarAffineHomeomorph_symm_apply (a : EuclideanPlane) (s : ℝ) (hs : s ≠ 0) (y : EuclideanPlane) :
    (planarAffineHomeomorph a s hs).symm y = s⁻¹ • (y-a) := rfl

lemma integral_planarAffine (a : EuclideanPlane) {s : ℝ} (hs : 0 < s)
    (h : EuclideanPlane → ℝ) :
    (∫ x, h (a+s • x)) = (s^2)⁻¹ * ∫ y, h y := by
  have he := Measure.integral_comp_smul_of_nonneg (E := EuclideanPlane) volume
    (fun y => h (a+y)) s (hR := hs.le)
  calc
    _ = (s ^ Module.finrank ℝ EuclideanPlane)⁻¹ • (∫ y, h (a+y)) := he
    _ = _ := by rw [finrank_euclideanSpace_fin, integral_add_left_eq_self, smul_eq_mul]

lemma planarAffine_inverse_hasFDerivAt (a : EuclideanPlane) {s : ℝ} (hs : s ≠ 0)
    (y : EuclideanPlane) :
    HasFDerivAt (planarAffineHomeomorph a s hs).symm
      (s⁻¹ • ContinuousLinearMap.id ℝ EuclideanPlane) y :=
  ((hasFDerivAt_id y).sub_const a).const_smul s⁻¹

end CircleDomainRigidity

end

end OAI

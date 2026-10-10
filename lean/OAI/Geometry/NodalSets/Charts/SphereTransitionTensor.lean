import OAI.Geometry.NodalSets.Charts.IntrinsicChartTensor
import OAI.Geometry.NodalSets.Charts.SphereTransitionFrame

namespace OAI

noncomputable section

namespace Yau.Geometry
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

lemma frameLeftInverse_transition (F : Matrix m n ℝ) (J : Matrix n n ℝ) (hJ : J.det ≠ 0) :
    frameLeftInverse (F*J) = J⁻¹*frameLeftInverse F := by
  have hg : (F*J).transpose*(F*J) = J.transpose*(F.transpose*F)*J := by simp [Matrix.mul_assoc]
  have ht : IsUnit J.transpose.det := by simpa using (isUnit_iff_ne_zero.mpr hJ)
  rw [frameLeftInverse,hg,Matrix.mul_inv_rev,Matrix.mul_inv_rev,transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc J.transpose⁻¹ J.transpose F.transpose,Matrix.nonsing_inv_mul _ ht,Matrix.one_mul]
  rfl

lemma frameContravariant_transition (A : Matrix m m ℝ) (F : Matrix m n ℝ)
    (J : Matrix n n ℝ) (hJ : J.det ≠ 0) :
    frameContravariant A (F*J) = J⁻¹*frameContravariant A F*J⁻¹.transpose := by
  simp only [frameContravariant_pullback,frameLeftInverse_transition F J hJ,
    transpose_mul,Matrix.mul_assoc]

end Yau.Geometry
namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Matrix

lemma sphereChartTransition_tensor (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (p q : Base) {x : Yau.Jets.Coord} (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartTensor A p (seedCoordEquiv x) =
      (jacobian (sphereChartTransition p q) x)⁻¹ *
        sphereChartTensor A q (seedCoordEquiv (sphereChartTransition p q x)) *
          ((jacobian (sphereChartTransition p q) x)⁻¹).transpose := by
  change frameContravariant (A (sphereChartCoordMap p x)) (sphereChartFrame p (seedCoordEquiv x)) =
    _*frameContravariant (A (sphereChartCoordMap q (sphereChartTransition p q x))) _*_
  rw [sphereChartTransition_point p q hx,sphereChartTransition_frame p q hx,
    frameContravariant_transition _ _ _ (sphereChartTransition_jacobian_ne_zero p q hx)]

lemma sphereChartTransition_intrinsic_tensor (A : IntrinsicTensor)
    (p q : Base) {x : Yau.Jets.Coord} (hx : x ∈ sphereChartTransitionDomain p q) :
    intrinsicSphereChartTensor A p (seedCoordEquiv x) =
      (jacobian (sphereChartTransition p q) x)⁻¹ *
        intrinsicSphereChartTensor A q (seedCoordEquiv (sphereChartTransition p q x)) *
          ((jacobian (sphereChartTransition p q) x)⁻¹).transpose := by
  simp only [intrinsicSphereChartTensor_eq]
  exact sphereChartTransition_tensor _ p q hx

end Yau.Target

end

end OAI

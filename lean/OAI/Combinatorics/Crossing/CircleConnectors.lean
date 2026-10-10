import OAI.Combinatorics.Crossing.CircleOffset
import OAI.Combinatorics.Crossing.CircleOffsetParameter
import OAI.Combinatorics.Crossing.MovingSegmentStability

namespace OAI

noncomputable section
namespace Zarankiewicz

def circleTangentOffset (u : Plane) (δ : ℝ) : Plane := u+δ • rotateQuarter u

theorem squaredLength_radial (u : Plane) (hu : squaredLength u=1) (a b : ℝ) :
    squaredLength (a • u+b • rotateQuarter u)=a^2+b^2 := by
  have he : squaredLength (a • u+b • rotateQuarter u)=(a^2+b^2)*squaredLength u := by
    dsimp [squaredLength,rotateQuarter]
    ring
  rw [he,hu,mul_one]

theorem circleConnector_parameterization (u : Plane) (δ t : ℝ) :
    segmentPoint (circleOffset u δ) (circleTangentOffset u δ) t =
      ((1-t)*Real.sqrt (1-δ^2)+t) • u+δ • rotateQuarter u := by
  apply Prod.ext <;> dsimp [segmentPoint,circleOffset,circleTangentOffset,rotateQuarter] <;> ring

theorem circleConnector_outside (u : Plane) (hu : squaredLength u=1)
    (δ : ℝ) (hδ : |δ|≤1) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    1 ≤ squaredLength (segmentPoint (circleOffset u δ) (circleTangentOffset u δ) t) := by
  have hnon : 0 ≤ 1-δ^2 := by have hh := abs_le.mp hδ; nlinarith
  have hs := Real.sq_sqrt hnon
  have hs0 := Real.sqrt_nonneg (1-δ^2)
  have hs1 : Real.sqrt (1-δ^2) ≤ 1 := by nlinarith [sq_nonneg δ]
  have hA : Real.sqrt (1-δ^2) ≤ (1-t)*Real.sqrt (1-δ^2)+t := by
    have hmul := mul_nonneg ht.1 (sub_nonneg.mpr hs1)
    nlinarith
  rw [circleConnector_parameterization,squaredLength_radial u hu]
  nlinarith

theorem circleConnector_strictly_outside (u : Plane) (hu : squaredLength u=1)
    (δ : ℝ) (hδ : |δ|<1) (hne : δ ≠ 0) (t : ℝ) (ht : 0<t) :
    1 < squaredLength (segmentPoint (circleOffset u δ) (circleTangentOffset u δ) t) := by
  have hnon : 0 ≤ 1-δ^2 := by have hh := abs_lt.mp hδ; nlinarith
  have hs := Real.sq_sqrt hnon
  have hs0 := Real.sqrt_nonneg (1-δ^2)
  have hs1 : Real.sqrt (1-δ^2) < 1 := by nlinarith [sq_pos_of_ne_zero hne]
  have hA : Real.sqrt (1-δ^2) < (1-t)*Real.sqrt (1-δ^2)+t := by
    have hmul := mul_pos ht (sub_pos.mpr hs1)
    nlinarith
  rw [circleConnector_parameterization,squaredLength_radial u hu]
  nlinarith

theorem circleConnector_side (u : Plane) (hu : squaredLength u=1) (δ t : ℝ) :
    det2 u (segmentPoint (circleOffset u δ) (circleTangentOffset u δ) t)=δ := by
  rw [circleConnector_parameterization,det2_add_right,det2_smul_right,det2_self,mul_zero]
  have he : det2 u (rotateQuarter u)=squaredLength u := by
    dsimp [det2,rotateQuarter,squaredLength]
    ring
  rw [det2_smul_right,he,hu,mul_one,zero_add]

end Zarankiewicz

end

end OAI

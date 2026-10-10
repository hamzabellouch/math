import OAI.Combinatorics.Crossing.CircleParameterChart
import OAI.Combinatorics.Crossing.OffsetVectors
import Mathlib.Analysis.Real.Sqrt

namespace OAI

noncomputable section
namespace Zarankiewicz

def circleOffset (u : Plane) (δ : ℝ) : Plane := Real.sqrt (1-δ^2) • u+δ • rotateQuarter u

theorem circleOffset_on_circle (u : Plane) (hu : squaredLength u=1) (δ : ℝ) (hδ : |δ|≤1) :
    squaredLength (circleOffset u δ)=1 := by
  have hnon : 0 ≤ 1-δ^2 := by
    have h := abs_le.mp hδ
    nlinarith
  have hs := Real.sq_sqrt hnon
  have he : squaredLength (circleOffset u δ)=
      ((Real.sqrt (1-δ^2))^2+δ^2)*squaredLength u := by
    dsimp [squaredLength,circleOffset,rotateQuarter]
    ring
  rw [he,hu,hs]
  ring

theorem circleOffset_side (u : Plane) (hu : squaredLength u=1) (δ : ℝ) :
    det2 u (circleOffset u δ)=δ := by
  dsimp [circleOffset,det2,rotateQuarter,squaredLength] at *
  linear_combination δ*hu

@[simp] theorem circleOffset_zero (u : Plane) : circleOffset u 0=u := by
  simp [circleOffset]

end Zarankiewicz

end

end OAI

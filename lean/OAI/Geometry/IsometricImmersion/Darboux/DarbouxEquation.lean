import OAI.Geometry.IsometricImmersion.Darboux.DarbouxJet
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem solvedDarboux_at_height
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    coordPartial 0 (coordPartial 0 z) p =
      solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  have hsolve : covHessian g z p 0 0 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 1 1 := by
    apply (eq_div_iff hyy).2
    linarith [hdet]
  change coordPartial 0 (coordPartial 0 z) p -
    jetConnection g p 0 0 (fun i => coordPartial i z p) = _ at hsolve
  rw [solvedDarboux, jetNumerator, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z]
  linarith [hsolve]

theorem darbouxDet_of_solved_at_height
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (hP : coordPartial 0 (coordPartial 0 z) p =
      solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p)) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p := by
  rw [solvedDarboux, jetNumerator, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z] at hP
  have hsolve : covHessian g z p 0 0 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 1 1 := by
    change coordPartial 0 (coordPartial 0 z) p -
      jetConnection g p 0 0 (fun i => coordPartial i z p) = _
    linarith [hP]
  have hmul := (eq_div_iff hyy).1 hsolve
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    linarith [hmul]
  simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hdet

theorem darbouxDet_iff_solved_at_height
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p ↔
      coordPartial 0 (coordPartial 0 z) p =
        solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
          (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) :=
  ⟨solvedDarboux_at_height hg hU hz hp hyy,
    darbouxDet_of_solved_at_height hg hU hz hp hyy⟩

end SmoothLocal.Geometry

end

end OAI

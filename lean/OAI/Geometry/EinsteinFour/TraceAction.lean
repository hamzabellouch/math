import OAI.Geometry.EinsteinFour.TraceActionIntertwining
import OAI.Geometry.EinsteinFour.GradientProjection

namespace OAI

/-! The precise curvature action on the prescribed trace component. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi HighestHessian

theorem traceLift_add (M N : Mat) : traceLift (M + N) = traceLift M + traceLift N := by
  funext i j a b
  by_cases hij : i = j <;>
    simp [traceLift, matrixAction, hij, mul_add, add_mul, Finset.sum_add_distrib]
  all_goals simp only [Fin.sum_univ_three]
  all_goals ring

theorem traceLift_smul (r : ℝ) (M : Mat) : traceLift (r • M) = r • traceLift M := by
  funext i j a b
  by_cases hij : i = j <;>
    simp [traceLift, matrixAction, hij, Fin.sum_univ_three]
  all_goals ring

theorem traceLift_sub (M N : Mat) : traceLift (M - N) = traceLift M - traceLift N := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ N, traceLift_add, traceLift_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

theorem traceLift_weighted_sum (t : Fin 3 → ℝ) (f : Fin 3 → Mat) :
    traceLift (∑ s, t s • f s) = ∑ s, t s • traceLift (f s) := by
  simp only [Fin.sum_univ_three, traceLift_add, traceLift_smul]

private theorem pairing_weighted_sum (t : Fin 3 → ℝ) (f : Fin 3 → Hessian)
    (Y : Hessian) :
    hessianPairing (∑ s, t s • f s) Y = ∑ s, t s * hessianPairing (f s) Y := by
  simp only [Fin.sum_univ_three, hessianPairing_add_left, hessianPairing_smul_left]

/-- The trace adjoint intertwines the total plus action and kills the minus
action, so its curvature action is exactly `4 - B_F(t)`. -/
theorem traceLift_curvatureAction (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (M : Mat) (hs : symmetric M) (hm : traceFree M) (Y : Hessian) :
    curvaturePairing t u (traceLift M) Y =
      hessianPairing (traceLift ((4 : ℝ) • M - diagonalCurvatureAction t M)) Y := by
  have hp (s : Fin 3) :
      hessianPairing (totalPlus s (traceLift M)) (totalPlus s Y) =
        -hessianPairing (traceLift (matrixAction s (matrixAction s M))) Y := by
    have h := totalPlus_skew s (traceLift (matrixAction s M)) Y
    rw [totalPlus_traceLift] at h
    rw [totalPlus_traceLift]
    linarith
  have hw : (∑ s, t s *
      hessianPairing (traceLift (matrixAction s (matrixAction s M))) Y) =
        24 * hessianPairing (traceLift (diagonalCurvatureAction t M)) Y := by
    rw [← pairing_weighted_sum, ← traceLift_weighted_sum,
      weighted_matrixAction_square t ht M hs hm, traceLift_smul,
      hessianPairing_smul_left]
  have hzero (V : Hessian) : hessianPairing (0 : Hessian) V = 0 := by simp [hessianPairing]
  rw [traceLift_sub, traceLift_smul]
  have hsub : hessianPairing ((4 : ℝ) • traceLift M -
      traceLift (diagonalCurvatureAction t M)) Y =
        4 * hessianPairing (traceLift M) Y -
          hessianPairing (traceLift (diagonalCurvatureAction t M)) Y := by
    rw [sub_eq_add_neg, ← neg_one_smul ℝ (traceLift (diagonalCurvatureAction t M)),
      hessianPairing_add_left, hessianPairing_smul_left, hessianPairing_smul_left]
    ring
  rw [hsub]
  simp only [curvaturePairing, hp, totalMinus_traceLift, hzero,
    mul_neg, Finset.sum_neg_distrib, mul_zero, Finset.sum_const_zero, zero_div, add_zero]
  rw [hw]
  ring

/-- The normalization `5/12` commutes with the exact trace curvature action. -/
theorem traceComponent_curvatureAction (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (M : Mat) (hs : symmetric M) (hm : traceFree M) (Y : Hessian) :
    curvaturePairing t u (traceComponent M) Y =
      hessianPairing (traceComponent ((4 : ℝ) • M - diagonalCurvatureAction t M)) Y := by
  change curvaturePairing t u ((5 / 12 : ℝ) • traceLift M) Y =
    hessianPairing ((5 / 12 : ℝ) •
      traceLift ((4 : ℝ) • M - diagonalCurvatureAction t M)) Y
  rw [curvaturePairing_smul_left, hessianPairing_smul_left,
    traceLift_curvatureAction t u ht M hs hm Y]

end
end PositiveEinsteinFour.TraceHessian

end OAI

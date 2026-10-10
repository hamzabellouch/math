import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

noncomputable section
open scoped ENNReal ComplexConjugate
namespace Invariant233.WeightedShift

@[simp] theorem diagonalAlgHom_apply (w : Weight) : diagonalAlgHom w = diagonal w := rfl

@[simp] theorem diagonal_one : diagonal (1 : Weight) = 1 := diagonalAlgHom.map_one
@[simp] theorem diagonal_zero : diagonal (0 : Weight) = 0 := diagonalAlgHom.map_zero
@[simp] theorem diagonal_add (w v : Weight) : diagonal (w + v) = diagonal w + diagonal v :=
  diagonalAlgHom.map_add w v
@[simp] theorem diagonal_mul (w v : Weight) : diagonal (w * v) = diagonal w * diagonal v :=
  diagonalAlgHom.map_mul w v
@[simp] theorem diagonal_smul (c : ℂ) (w : Weight) : diagonal (c • w) = c • diagonal w :=
  diagonalAlgHom.toLinearMap.map_smul c w

@[simp] theorem diagonal_star (w : Weight) : diagonal (star w) = star (diagonal w) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro ξ η
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp only [diagonal_apply, lp.coeFn_star, Pi.star_apply, RCLike.inner_apply,
    map_mul, starRingEnd_apply, star_star]
  ring

@[simp] theorem translate_apply (w : Weight) (m k : ℤ) : translate w m k = w (k + m) := rfl

@[simp] theorem translate_zero (w : Weight) : translate w 0 = w := by
  ext k
  simp

@[simp] theorem translate_add (w : Weight) (m n : ℤ) :
    translate w (m + n) = translate (translate w n) m := by
  ext k
  simp [add_assoc]

theorem diagonal_shift_covariance (w : Weight) (m : ℤ) :
    diagonal w * (shift m).toLinearIsometry.toContinuousLinearMap =
      (shift m).toLinearIsometry.toContinuousLinearMap * diagonal (translate w m) := by
  ext ξ k
  change w k * ξ (k - m) = w (k - m + m) * ξ (k - m)
  simp

theorem shift_add (m n : ℤ) :
    (shift (m + n)).toLinearIsometry.toContinuousLinearMap =
      (shift m).toLinearIsometry.toContinuousLinearMap *
        (shift n).toLinearIsometry.toContinuousLinearMap := by
  ext ξ k
  change ξ (k - (m + n)) = ξ (k - m - n)
  exact congrArg (fun q : ℤ => ξ q) (by omega)

@[simp] theorem shift_zero : (shift 0).toLinearIsometry.toContinuousLinearMap = 1 := by
  ext ξ k
  change ξ (k - 0) = ξ k
  simp

theorem conjugate_diagonal (w : Weight) (m : ℤ) :
    (shift (-m)).toLinearIsometry.toContinuousLinearMap * diagonal w *
      (shift m).toLinearIsometry.toContinuousLinearMap = diagonal (translate w m) := by
  rw [mul_assoc, diagonal_shift_covariance, ← mul_assoc, ← shift_add]
  simp

theorem diagonal_injective : Function.Injective diagonal := by
  intro w v h
  ext k
  have h' := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (lp.single 2 k 1) k) h
  simpa using h'

end Invariant233.WeightedShift

end

end OAI

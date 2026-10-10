import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace SmoothLocal.DriftAlgebra

theorem energy_first_jet_contraction
    (gxx gxy gyy zx zy q : ℝ) :
    q * (-2 * (gyy * zx - gxy * zy)) +
      (-2 * (-gxy * zx + gxx * zy)) =
      -2 * ((gxx - q * gxy) * zy - (gxy - q * gyy) * zx) := by
  ring

theorem explicit_drift_remainder
    (h E hy q cxy cyy dyy J ex ey Ey : ℝ)
    (hne : h ≠ 0)
    (energy_y : Ey = 2 * (cxy + dyy) * E - 2 * h * J)
    (energy_jet : q * ex + ey = -2 * J) :
    (Ey / h ^ 2 - E * hy / h ^ 3 - E * (cxy - q * cyy) / h ^ 2 + J / h) -
        q * (ex / h + E * cyy / h ^ 2) - (ey / h + E * dyy / h ^ 2) =
      E / h ^ 2 * (cxy + dyy - hy / h) + J / h := by
  have hey : ey = -2 * J - q * ex := by linarith [energy_jet]
  rw [energy_y, hey]
  field_simp [hne]
  ring

theorem transverse_coefficient_polynomial
    (ell K Ky G Gy rho sigma R : ℝ) :
    K * G * sigma + rho * (Ky * G + K * R + ell * (Ky * G + K * Gy)) =
      (ell + 1) * (G * rho * Ky + K * (rho * Gy + 2 * G * sigma)) +
        K * (rho * R - rho * Gy - (2 * ell + 1) * G * sigma) := by
  ring

theorem transverse_coefficient_factor
    (ell K G Gy rho sigma R : ℝ) (hG : G ≠ 0) (hrho : rho ≠ 0) :
    K * (rho * R - rho * Gy - (2 * ell + 1) * G * sigma) =
      (K * G * rho ^ 2) *
        ((R - Gy) / (G * rho) - (2 * ell + 1) * sigma / rho ^ 2) := by
  field_simp [hG, hrho]

end SmoothLocal.DriftAlgebra

end OAI

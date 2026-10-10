import OAI.Geometry.IsometricImmersion.Darboux.Drift

namespace OAI

namespace SmoothLocal.DriftAlgebra

theorem quotient_transport_algebra
    (A B h Ay Bx By hx hy K Ky E Ey a b c d e f J0 J1 : ℝ)
    (hne : h ≠ 0)
    (hdet : A * h - B ^ 2 = K * E)
    (hdety : Ay * h + A * hy - 2 * B * By = Ky * E + K * Ey)
    (hBx : Bx - Ay = -b * A + (a - e) * B + d * h + K * J0)
    (hhx : hx - By = -c * A + (b - f) * B + e * h + K * J1) :
    (Bx - (B / h) * By) / h - (B / h) * (hx - (B / h) * hy) / h -
      (B / h) * (a - 2 * (B / h) * b + (B / h) ^ 2 * c) -
      (d - 2 * (B / h) * e + (B / h) ^ 2 * f) =
        Ky * (E / h ^ 2) + K *
          (Ey / h ^ 2 - E * hy / h ^ 3 -
            (E / h ^ 2) * (b - (B / h) * c) + (J0 - (B / h) * J1) / h) := by
  have hA : A = (B ^ 2 + K * E) / h :=
    (eq_div_iff hne).2 (by linarith [hdet])
  have hAy : Ay = (Ky * E + K * Ey - A * hy + 2 * B * By) / h :=
    (eq_div_iff hne).2 (by linarith [hdety])
  have hBx' : Bx = Ay - b * A + (a - e) * B + d * h + K * J0 := by
    linarith [hBx]
  have hhx' : hx = By - c * A + (b - f) * B + e * h + K * J1 := by
    linarith [hhx]
  rw [hBx', hhx', hAy, hA]
  field_simp [hne]
  ring

end SmoothLocal.DriftAlgebra

end OAI

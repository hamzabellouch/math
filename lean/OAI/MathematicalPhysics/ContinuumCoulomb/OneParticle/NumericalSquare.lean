import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RectangleQuadrature

namespace OAI

/-! Squaring a computed value is uniformly stable on the range of the
constructed planar resolvent. -/

namespace ContinuumCoulomb

theorem unitInterval_square_error {a b ε : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hε : ε ≤ 1) (herr : |a - b| ≤ ε) : |a ^ 2 - b ^ 2| ≤ 3 * ε := by
  have he0 : 0 ≤ ε := (abs_nonneg _).trans herr
  have ha : |a| ≤ 2 := by
    have h := abs_add_le (a - b) b
    rw [sub_add_cancel, abs_of_nonneg hb0] at h
    linarith
  have hs : |a + b| ≤ 3 := (abs_add_le a b).trans (by
    rw [abs_of_nonneg hb0]
    linarith)
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul]
  calc
    _ ≤ ε * 3 := mul_le_mul herr hs (abs_nonneg _) he0
    _ = _ := by ring

end ContinuumCoulomb

end OAI

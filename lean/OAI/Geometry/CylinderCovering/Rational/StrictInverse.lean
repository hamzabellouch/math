import OAI.Geometry.CylinderCovering.Rational.InverseSum

namespace OAI

theorem SlopeRational.InverseSum.actual_inverse_sum_strict {d : ℝ} (hd : 0 < d) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (e x y t : ℝ) (P Q : SlopeRational.Plane),
        0 ≤ e → e < δ → |x| ≤ 1 / 2 → |y| ≤ 1 / 2 →
        P ∈ SlopeRational.wedge → Q ∈ SlopeRational.wedge → P 1 < 0 → Q 1 < 0 →
        SlopeRational.tiltedMap d (e * x) P = SlopeRational.vec2 y t →
        SlopeRational.tiltedMap d (-e * y) Q = SlopeRational.vec2 x (-t) →
        |P 1 + Q 1 + e ^ 2 * SlopeRational.alpha d *
          (x ^ 2 * SlopeRational.ceilingCoefficient d y +
            y ^ 2 * SlopeRational.ceilingCoefficient d x)| ≤ C * e ^ 3 := by
  obtain ⟨δ, C, hδ, hC, h⟩ := SlopeRational.InverseSum.actual_inverse_sum hd
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro epsilon xCoord yCoord time pointP pointQ he heδ hx hy hP hQ hT hR hPm hQm
  exact h epsilon xCoord yCoord time pointP pointQ he heδ hx hy hP hQ hT.le hR.le hPm hQm

end OAI

import OAI.Geometry.CylinderCovering.Rational.Potential

namespace OAI

open scoped ContDiff

theorem SlopeRational.potential_contDiffAt_apex {d : ℝ} (hd : 0 < d) :
    ContDiffAt ℝ ∞ (fun z : SlopeRational.Plane =>
      SlopeRational.potential d (z 0) (z 1)) (SlopeRational.vec2 0 (1 / 2)) := by
  apply SlopeRational.potential_contDiffAt
  simpa [SlopeRational.vec2, SlopeRational.radius] using hd.ne'

theorem SlopeRational.potential_zero_half_height_homogeneous (c Y : ℝ) :
    SlopeRational.potential 0 (c * Y) (1 / 2) =
      c * SlopeRational.potential 0 Y (1 / 2) := by
  simpa using SlopeRational.potential_zero_homogeneous c Y 0

end OAI

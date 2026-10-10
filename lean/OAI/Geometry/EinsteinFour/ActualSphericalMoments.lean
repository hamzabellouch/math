import OAI.Geometry.EinsteinFour.SphericalSixthMoment
import OAI.Geometry.EinsteinFour.SphericalMeasureMass

namespace OAI

/-! The degree-two, four and six Folland formulas for the actual normalized
Hausdorff measure. Both the moments and its probability normalization are
proved here, so the geometric application need not assume them. -/

namespace PositiveEinsteinFour.Angular

theorem actual_follandMoments : FollandMoments := by
  let := actual_sphereMeasure_probability
  exact follandMoments_of_probability

end PositiveEinsteinFour.Angular

end OAI

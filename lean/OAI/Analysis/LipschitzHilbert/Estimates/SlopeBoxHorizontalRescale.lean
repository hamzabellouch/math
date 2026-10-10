import OAI.Analysis.LipschitzHilbert.Estimates.TopWeight

namespace OAI

/-! Covariance of the physical slope boxes under horizontal dilation. -/

noncomputable section
namespace LipschitzHilbert.SlopeBox

def horizontalRescale (T : SlopeBox) (r : ℝ) (hr : 0 < r) : SlopeBox where
  x := T.x/r
  y := T.y
  slope := r*T.slope
  length := T.length/r
  width := T.width
  length_pos := div_pos T.length_pos hr
  width_pos := T.width_pos

theorem horizontalRescale_horizontal (T : SlopeBox) (r : ℝ) (hr : 0 < r) (z : ℝ × ℝ) :
    (T.horizontalRescale r hr).horizontal z = T.horizontal (r*z.1,z.2) := by
  unfold horizontal horizontalRescale
  dsimp
  field_simp

theorem horizontalRescale_transverse (T : SlopeBox) (r : ℝ) (hr : 0 < r) (z : ℝ × ℝ) :
    (T.horizontalRescale r hr).transverse z = T.transverse (r*z.1,z.2) := by
  unfold transverse horizontalRescale
  dsimp
  field_simp

theorem horizontalRescale_radius (T : SlopeBox) (r : ℝ) (hr : 0 < r) (z : ℝ × ℝ) :
    (T.horizontalRescale r hr).radius z = T.radius (r*z.1,z.2) := by
  simp only [radius,horizontalRescale_horizontal,horizontalRescale_transverse]

theorem horizontalRescale_weight (T : SlopeBox) (r : ℝ) (hr : 0 < r) (K D : ℝ) (z : ℝ × ℝ) :
    (T.horizontalRescale r hr).weight K D z = T.weight K D (r*z.1,z.2) := by
  simp only [weight,horizontalRescale_radius]

theorem horizontalRescale_intercept (T : SlopeBox) (r : ℝ) (hr : 0 < r) :
    (T.horizontalRescale r hr).y - (T.horizontalRescale r hr).slope*(T.horizontalRescale r hr).x =
      T.y-T.slope*T.x := by
  change T.y-(r*T.slope)*(T.x/r) = _
  field_simp

theorem horizontalRescale_area (T : SlopeBox) (r : ℝ) (hr : 0 < r) :
    (T.horizontalRescale r hr).length*(T.horizontalRescale r hr).width = (T.length*T.width)/r := by
  change (T.length/r)*T.width = _
  ring

end LipschitzHilbert.SlopeBox

end

end OAI

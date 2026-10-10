import OAI.Geometry.CylinderCovering.Radial.OverlapQuantitativeDefinitions
import OAI.Geometry.CylinderCovering.Radial.OverlapBounds

namespace OAI

noncomputable section
namespace CylinderCovering.RadialOverlapQuantitative

open RadialOverlap RadialOverlapBounds

theorem canonical : CanonicalStatement := by
  intro eps x y t p q heps hx hy hp hq hroots hrho hsigma
  obtain ⟨hrootq, hrootp⟩ := hroots
  have hl : eps * y * p ≤ t := by
    dsimp [sigma] at hsigma
    linarith only [hsigma]
  have hu : t ≤ eps * x * q := by
    dsimp [rho] at hrho
    linarith only [hrho]
  obtain ⟨ht, hxp, hyq⟩ := root_estimates heps.le hx hy hp hq hrootq hrootp hl hu
  obtain ⟨_, hsum, hr0, hr, hs0, hs, hdiff⟩ :=
    joint_radial_bounds heps.le hx hy hp hq hrootq hrootp hrho hsigma
  exact ⟨ht, hxp, hyq, excess_identity eps x y t p q, hr0, hr, hs0, hs,
    hsum, hdiff.trans hsum, interface_error heps.le hx hy hp hq hrootq hrootp hl hu,
    cap_comparison heps.le hx hy hp hq hrootq hrootp hl hu,
    cubic_twelve_compensation heps hx hy hp hq hrootq hrootp hl hu⟩

theorem physical : PhysicalStatement := by
  intro tau x y z p q htau hx hy hp hq hrootq hrootp hl hu
  have hx2 : |x| ≤ 2 := by linarith only [hx, hy, abs_nonneg y]
  have hy2 : |y| ≤ 2 := by linarith only [hx, hy, abs_nonneg x]
  exact ⟨physical_cap_comparison (by positivity) htau.le hx2 hy2 hp hq hrootq hrootp hl hu,
    orthonormal_height_compensation htau hx2 hy2 hp hq hrootq hrootp hl hu⟩

theorem quantitative_overlap : Statement := ⟨canonical, physical⟩

end CylinderCovering.RadialOverlapQuantitative

end

end OAI

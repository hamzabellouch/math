import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.RadialSweep

def zeroCapData (D : Data) : Data where
  e := D.e
  a := D.a
  b := D.b
  p₀ := 0
  α := D.α
  β := D.β
  L := D.L
  R := fun _ => 0
  lam := fun _ => 0
  w := fun _ => 0
  interval_nonempty := D.interval_nonempty
  length_pos := D.length_pos
  normal_unit := D.normal_unit
  a_perp := D.a_perp
  b_perp := D.b_perp
  origin_perp := by simp
  independent := D.independent
  cap_continuous := continuousOn_const
  cap_nonneg := by intro _ _; exact le_rfl
  scalar_continuous := continuousOn_const
  velocity_continuous := continuousOn_const
  velocity_perp := by intro _ _; simp
  aligned := by
    intro t _
    simpa only [zero_smul] using
      (hasDerivWithinAt_const t (Icc D.α D.β) (0 : Space))

end CylinderCovering.RadialSweep

end

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialUniformEvaluation

namespace OAI

/-! The completed radial representative is continuous throughout the positive-radius domain. -/

open Set
namespace DefocusingNLS

theorem spectralRadialRepresentative_continuousOn_open (R : ℝ) (hR : 0 < R)
    (u : SpectralRadialEnergy R) :
    ContinuousOn (spectralRadialRepresentative R hR u) (Ioo 0 R) := by
  intro x hx
  have ha : 0 < x/2 := by linarith [hx.1]
  have hax : x/2 < x := by linarith [hx.1]
  exact ((spectralRadialRepresentative_continuousOn R (x/2) hR ha u).continuousAt
    (Icc_mem_nhds hax hx.2)).continuousWithinAt

end DefocusingNLS

end OAI

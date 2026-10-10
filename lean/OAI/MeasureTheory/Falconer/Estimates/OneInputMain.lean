import OAI.MeasureTheory.Falconer.Estimates.TwoInputsMain
import OAI.MeasureTheory.Falconer.Radial.RadialDischarge

namespace OAI

namespace Falconer

/-- Exact all-dimensional conclusion after independently proving the radial input. -/
theorem mainTarget_of_planar_furstenberg
    (hFurstenberg : PublishedPlanarFurstenberg) : MainTarget :=
  mainTarget_of_two_published_inputs published_radial_moment hFurstenberg

end Falconer

end OAI

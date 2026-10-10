import OAI.MeasureTheory.Falconer.Estimates.FourInputsMain
import OAI.MeasureTheory.Falconer.Radial.HeavyDischarge

namespace OAI

/-! # The exact main theorem after the heavy-hyperplane discharge -/
namespace Falconer

theorem mainTarget_of_three_published_inputs
    (hRadial : PublishedRadialMoment)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget :=
  mainTarget_of_four_published_inputs hRadial published_heavy_hyperplanes
    hFurstenberg hQuadratic

end Falconer

end OAI

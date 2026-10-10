import OAI.MeasureTheory.Falconer.Estimates.SixInputsMain
import OAI.MeasureTheory.Falconer.Radial.PlanarRadialDischarge

namespace OAI

/-! # The main theorem after three proved inputs and dimension descent -/
namespace Falconer

theorem mainTarget_of_five_published_inputs
    (hFrostman : PublishedFrostmanAboveHalf)
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget :=
  mainTarget_of_six_published_inputs PlanarFalconer.published_planar_radial_moment
    hFrostman hRadial hHeavy hFurstenberg hQuadratic

end Falconer

end OAI

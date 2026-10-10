import OAI.MeasureTheory.Falconer.Estimates.ReducedInputsMain
import OAI.MeasureTheory.Falconer.Angular.GnomonicDischarge

namespace OAI

/-! # The main distance theorem from seven analytic hypotheses -/
namespace Falconer

theorem mainTarget_of_seven_published_inputs
    (hPlanar : PlanarFalconer.PublishedPlanarRadialMoment)
    (hFrostman : PublishedFrostmanAboveHalf)
    (hClassical : PublishedClassicalDistance)
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget :=
  mainTarget_of_eight_published_inputs hPlanar hFrostman hClassical hRadial hHeavy
    hFurstenberg published_gnomonic_surface hQuadratic

end Falconer

end OAI

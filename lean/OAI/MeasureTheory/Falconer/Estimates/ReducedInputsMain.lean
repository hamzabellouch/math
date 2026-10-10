import OAI.MeasureTheory.Falconer.Estimates.AllDimensionalMain
import OAI.MeasureTheory.Falconer.Incidence.FiniteLatticeLoomis

namespace OAI

/-! # The all-dimensional main theorem after finite projection-count discharge -/
namespace Falconer

theorem mainTarget_of_eight_published_inputs
    (hPlanar : PlanarFalconer.PublishedPlanarRadialMoment)
    (hFrostman : PublishedFrostmanAboveHalf)
    (hClassical : PublishedClassicalDistance)
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hGnomonic : PublishedGnomonicSurface)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget :=
  mainTarget_of_published_inputs hPlanar hFrostman hClassical hRadial hHeavy
    hFurstenberg published_finite_loomis_whitney hGnomonic hQuadratic

end Falconer

end OAI

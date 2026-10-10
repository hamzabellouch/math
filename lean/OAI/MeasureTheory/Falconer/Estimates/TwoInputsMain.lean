import OAI.MeasureTheory.Falconer.Estimates.ThreeInputsMain
import OAI.MeasureTheory.Falconer.Estimates.QuadraticDischarge

namespace OAI

namespace Falconer

theorem mainTarget_of_two_published_inputs
    (hRadial : PublishedRadialMoment)
    (hFurstenberg : PublishedPlanarFurstenberg) : MainTarget :=
  mainTarget_of_three_published_inputs hRadial hFurstenberg published_quadratic_stationary

end Falconer

end OAI

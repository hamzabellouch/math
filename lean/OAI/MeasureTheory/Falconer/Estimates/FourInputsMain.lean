import OAI.MeasureTheory.Falconer.Estimates.FiveInputsMain
import OAI.MeasureTheory.Falconer.Measures.FrostmanDischarge

namespace OAI

/-! # The main distance theorem from four analytic hypotheses -/
namespace Falconer

theorem mainTarget_of_four_published_inputs
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget :=
  mainTarget_of_five_published_inputs published_frostman_above_half
    hRadial hHeavy hFurstenberg hQuadratic

end Falconer

end OAI

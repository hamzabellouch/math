import OAI.Analysis.KadisonKastler.PublishedBicentralizerInputs
import OAI.Analysis.KadisonKastler.RemainingInputs

namespace OAI

/-! # Universal strong stability from state homogeneity and bicentralizers -/

namespace KadisonKastler

noncomputable section

universe u

/-- State homogeneity and Powers absorption for bicentralizers imply
universal strong stability. -/
theorem universal_strong_stability_of_state_inputs
    (hhom : PublishedTypeIII1StateHomogeneity.{u})
    (hbic : PublishedPowersAbsorptionBicentralizer.{u}) : UniversalStrongStability.{u} :=
  universal_strong_stability_of_remaining
    ⟨publishedExpectedMatrixSubfactor_of_state_inputs hhom hbic⟩

end

end KadisonKastler

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Finiteness.DualityEndgame
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoarsePoincareDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteResolutionTruncation

namespace OAI

/-! # Deriving the duality transfer from finiteness transfer

The cohomology comparison is proved by controlled cochains. Canonical
truncation supplies a finite projective resolution once FP infinity and finite
cohomological dimension are known. Thus the application of Li, Corollary 4.48,
requires no independent hypothesis beyond the Corollary 4.47 finiteness transfer.
-/

namespace PolycyclicRecognition

theorem liDualityInput_of_finiteness (liFP : LiFinitenessInput) : LiDualityInput := by
  intro Γ H _ _ _ _ e _ hcd n hPD
  have hfp : TypeFPInfinity H := fun k => liFP Γ H e k (hPD.typeFPInfinity Γ k)
  exact poincareDuality_of_coarse_finiteResolution e
    (finiteProjectiveResolution_of_finiteDimension_typeFP hcd hfp) hPD

end PolycyclicRecognition

end OAI

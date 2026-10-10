import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FinitenessFromControlledFillings
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.DualityEndgame
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.LiDualityFromFiniteness

namespace OAI

/-! # Coarse invariance of integral FP finiteness

The proof transfers uniform fillings and constructs finite projective covers.
It does not assume homology with product coefficients or an FP recognition
criterion.
-/

namespace PolycyclicRecognition

theorem liFinitenessInput : LiFinitenessInput := by
  intro Γ H _ _ _ _ e m hΓ
  apply typeFP_of_controlledCycleFillings m
  intro n hn
  exact ((hΓ.mono hn).controlledCycleFillings).of_coarse e

/-- Integral Poincaré duality transfers once both cohomological dimensions
are finite, using the proved FP transfer and controlled cochain comparison. -/
theorem liDualityInput : LiDualityInput :=
  liDualityInput_of_finiteness liFinitenessInput

end PolycyclicRecognition

end OAI

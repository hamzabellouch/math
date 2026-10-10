import Mathlib.Tactic.IntervalCases
import OAI.Analysis.Laughlin.FiniteFlux.Positive05
import OAI.Analysis.Laughlin.FiniteFlux.Positive07
import OAI.Analysis.Laughlin.FiniteFlux.Positive08
import OAI.Analysis.Laughlin.FiniteFlux.Positive09
import OAI.Analysis.Laughlin.FiniteFlux.Positive10
import OAI.Analysis.Laughlin.FiniteFlux.Positive11
import OAI.Analysis.Laughlin.FiniteFlux.Positive12
import OAI.Analysis.Laughlin.FiniteFlux.Positive13
import OAI.Analysis.Laughlin.FiniteFlux.Positive14
import OAI.Analysis.Laughlin.FiniteFlux.Positive15
import OAI.Analysis.Laughlin.FiniteFlux.Positive16
import OAI.Analysis.Laughlin.FiniteFlux.Positive17
import OAI.Analysis.Laughlin.FiniteFlux.Positive18
import OAI.Analysis.Laughlin.FiniteFlux.Positive19
import OAI.Analysis.Laughlin.FiniteFlux.Positive20
import OAI.Analysis.Laughlin.FiniteFlux.Positive21
import OAI.Analysis.Laughlin.FiniteFlux.Positive22
import OAI.Analysis.Laughlin.FiniteFlux.Positive23

namespace OAI

namespace Laughlin.Certificate

theorem four_body_certificates (D : ℕ) (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef := by
  interval_cases D
  · exact zero_blocks_positive 1 (by decide)
  · exact zero_blocks_positive 2 (by decide)
  · exact zero_blocks_positive 3 (by decide)
  · exact zero_blocks_positive 4 (by decide)
  · exact four_body_five_positive
  · exact zero_blocks_positive 6 (by decide)
  · exact four_body_7_positive
  · exact four_body_8_positive
  · exact four_body_9_positive
  · exact four_body_10_positive
  · exact four_body_11_positive
  · exact four_body_12_positive
  · exact four_body_13_positive
  · exact four_body_14_positive
  · exact four_body_15_positive
  · exact four_body_16_positive
  · exact four_body_17_positive
  · exact four_body_18_positive
  · exact four_body_19_positive
  · exact four_body_20_positive
  · exact four_body_21_positive
  · exact four_body_22_positive
  · exact four_body_23_positive

end Laughlin.Certificate

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProductDerivativeFormula
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPartialKernel
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSmoothCutoff

namespace OAI

/-! # The product rule for the actual sampled coefficient and smooth cutoff -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingSample_low_derivative_formula (a L R : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L) (hR : 0 < R)
    (j : Fin N → Fin 12) (K : 𝓢(E, ℂ)) (f : FourierL2) :
    expandingOrderedFourierEnergy a L N hL j
      (expandingProduct a N L ha ha1 hN hL
        (schwartzTorusSample a N L ha1 hN hL (radianFourierKernel K)) (expandingSmoothLow L R hR f)) =
      ∑ s : Finset (Fin N), expandingPhysicalMassVector a N L ha ha1 hN hL
        (expandingProduct a N L ha ha1 hN hL
          (schwartzTorusSample a N L ha1 hN hL
            (radianFourierKernel (schwartzPartialDerivative N j s K)))
          (expandingSchwartzFilter L (partialFilterKernel R hR N j sᶜ) f)) := by
  apply expandingProduct_derivative_formula a L N ha ha1 hN hL j
  · intro s n
    rw [schwartzTorusSample_coefficient, schwartzTorusSample_coefficient]
    simp only [schwartzLatticeCoefficient, schwartzPartialDerivative_fourier]
    ring
  · intro s n
    simp only [expandingFourierCoefficient, expandingSchwartzFilter_apply,
      expandingSmoothLow_apply, partialFilterKernel_fourier]
    ring

end DefocusingNLS

end OAI

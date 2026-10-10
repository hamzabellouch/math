import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactDerivativeLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMassDerivativeNorm

namespace OAI

/-! # Strong compactness of a sampled coefficient after smooth frequency cutoff -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_expandingSample_low_product (a M R S : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hS : 0 < S)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a N (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (K : 𝓢(E, ℂ)) (hK : ∀ y : E, R < ‖y‖ → K y = 0) :
    Tendsto (fun n => expandingProduct a N (L n) ha ha1 hN (hL n)
      (schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel K))
      (expandingSmoothLow (L n) S hS (f n))) atTop (𝓝 0) := by
  let q := fun n => schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel K)
  let u := fun n => expandingSmoothLow (L n) S hS (f n)
  let g := fun n => expandingProduct a N (L n) ha ha1 hN (hL n) (q n) (u n)
  apply tendsto_expanding_of_mass_derivatives_zero a N ha ha1 hN L hL g
  · have ht := tendsto_expandingCompactPhysical_filter a N M R ha ha1 hN L hL hLinf f hf hlocal
      (radianInverseKernel (smoothFrequencyCutoff S hS)) K hK
    have he (n : ℕ) : ‖expandingPhysicalMassVector a N (L n) ha ha1 hN (hL n) (g n)‖ =
        ‖torusPhysicalL2Value (L n) (expandingUnitTorusFunction a N (L n) (q n) *
          expandingUnitTorusFunction a N (L n)
            (expandingSchwartzFilter (L n) (radianInverseKernel (smoothFrequencyCutoff S hS)) (f n)))‖ := by
      rw [← LinearIsometryEquiv.norm_map torusFourierIsometry
        (expandingPhysicalMassVector a N (L n) ha ha1 hN (hL n) (g n)),
        expandingPhysicalMassVector_isometry]
      dsimp only [g]
      rw [expandingUnitTorusFunction_product]
      dsimp only [u]
      rw [expandingSmoothLow_eq_convolution]
    simpa only [he] using ht
  · intro j
    have ht := tendsto_expandingSample_low_derivative a M R S N ha ha1 hN hS
      L hL hLinf f hf hlocal K hK j
    simpa only [norm_zero] using ht.norm

end DefocusingNLS

end OAI

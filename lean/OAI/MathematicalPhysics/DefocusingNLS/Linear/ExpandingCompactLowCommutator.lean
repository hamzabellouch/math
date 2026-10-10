import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFilteredPhysicalEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactDerivativeLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactPhysicalLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusProductCommutator

namespace OAI

/-! # Compactness of the actual low-frequency product commutator -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_expandingSample_low_commutator (a M R S : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hS : 0 < S)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a N (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (K : 𝓢(E, ℂ)) (hK : ∀ y : E, R < ‖y‖ → K y = 0) (j : Fin N → Fin 12) :
    Tendsto (fun n => expandingProductCommutator a (L n) N ha ha1 hN (hL n) j
      (schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel K))
      (expandingSmoothLow (L n) S hS (f n))) atTop (𝓝 0) := by
  let q := fun n => schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel K)
  let u := fun n => expandingSmoothLow (L n) S hS (f n)
  have hfirst := tendsto_expandingSample_low_derivative a M R S N ha ha1 hN hS
    L hL hLinf f hf hlocal K hK j
  have hfirst' := (torusFourierIsometry.continuous.tendsto 0).comp hfirst
  have hsecond := tendsto_expandingCompactPhysical_derivative a N M R S ha ha1 hN hS
    N j L hL hLinf f hf hlocal K hK
  rw [← tendsto_zero_iff_norm_tendsto_zero] at hsecond
  have he (n : ℕ) : torusFourierIsometry
      (expandingProductCommutator a (L n) N ha ha1 hN (hL n) j (q n) (u n)) =
      torusFourierIsometry (expandingOrderedFourierEnergy a (L n) N (hL n) j
        (expandingProduct a N (L n) ha ha1 hN (hL n) (q n) (u n))) -
      torusPhysicalL2Value (L n) (expandingUnitTorusFunction a N (L n) (q n) *
        expandingUnitTorusFunction a N (L n) (expandingSmoothDerivative (L n) S hS N j (f n))) := by
    rw [torusProductCommutator_physical]
    dsimp only [u]
    rw [expandingOrderedPhysicalEnergy_smoothLow a (L n) S N ha ha1 hN (hL n) hS,
      torusL2Product_physical]
    rfl
  have ht := hfirst'.sub hsecond
  simp only [map_zero, sub_zero] at ht
  rw [tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto (fun n => torusFourierIsometry
    (expandingOrderedFourierEnergy a (L n) N (hL n) j
      (expandingProduct a N (L n) ha ha1 hN (hL n) (q n) (u n))) -
      torusPhysicalL2Value (L n) (expandingUnitTorusFunction a N (L n) (q n) *
        expandingUnitTorusFunction a N (L n) (expandingSmoothDerivative (L n) S hS N j (f n))))
    atTop (𝓝 0) at ht
  simp_rw [← he] at ht
  simpa only [LinearIsometryEquiv.norm_map, norm_zero] using ht.norm

end DefocusingNLS

end OAI

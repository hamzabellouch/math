import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSampleDerivativeFormula
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactFilterLimit

namespace OAI

/-! # Low-frequency derivative compactness for the actual sampled product -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_expandingSample_low_derivative (a M R S : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hS : 0 < S)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a N (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (K : 𝓢(E, ℂ)) (hK : ∀ y : E, R < ‖y‖ → K y = 0) (j : Fin N → Fin 12) :
    Tendsto (fun n => expandingOrderedFourierEnergy a (L n) N (hL n) j
      (expandingProduct a N (L n) ha ha1 hN (hL n)
        (schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel K))
        (expandingSmoothLow (L n) S hS (f n)))) atTop (𝓝 0) := by
  let G := fun s : Finset (Fin N) => schwartzPartialDerivative N j s K
  let Q := fun n (s : Finset (Fin N)) =>
    schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel (G s))
  let F := fun n (s : Finset (Fin N)) =>
    expandingSchwartzFilter (L n) (partialFilterKernel S hS N j sᶜ) (f n)
  let V := fun n (s : Finset (Fin N)) => expandingPhysicalMassVector a N (L n) ha ha1 hN (hL n)
    (expandingProduct a N (L n) ha ha1 hN (hL n) (Q n s) (F n s))
  have hv (s : Finset (Fin N)) : Tendsto (fun n => V n s) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht := tendsto_expandingCompactPhysical_filter a N M R ha ha1 hN L hL hLinf f hf hlocal
      (partialFilterKernel S hS N j sᶜ) (G s) (schwartzPartialDerivative_zero N j s K R hK)
    have he (n : ℕ) : ‖V n s‖ = ‖torusPhysicalL2Value (L n)
        (expandingUnitTorusFunction a N (L n) (Q n s) *
          expandingUnitTorusFunction a N (L n) (F n s))‖ := by
      rw [← LinearIsometryEquiv.norm_map torusFourierIsometry (V n s)]
      dsimp only [V]
      rw [expandingPhysicalMassVector_isometry, expandingUnitTorusFunction_product]
    change Tendsto (fun n => ‖torusPhysicalL2Value (L n)
      (expandingUnitTorusFunction a N (L n) (Q n s) *
        expandingUnitTorusFunction a N (L n) (F n s))‖) atTop (𝓝 0) at ht
    simpa only [he] using ht
  have hs := tendsto_finsetSum Finset.univ (fun s _ => hv s)
  have he (n : ℕ) : expandingOrderedFourierEnergy a (L n) N (hL n) j
      (expandingProduct a N (L n) ha ha1 hN (hL n)
        (schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel K))
        (expandingSmoothLow (L n) S hS (f n))) = ∑ s : Finset (Fin N), V n s :=
    expandingSample_low_derivative_formula a (L n) S N ha ha1 hN (hL n) hS j K (f n)
  simp_rw [← he] at hs
  simpa only [Finset.sum_const_zero] using hs

end DefocusingNLS

end OAI

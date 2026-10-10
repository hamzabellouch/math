import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalCharacterLipschitz
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFourierJetBound

namespace OAI

/-! # A radius-uniform spatial modulus for the actual Fourier realization -/

open Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem hasSum_expandingPhysical (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) (y : E) :
    HasSum (fun n => expandingFourierCoefficient a k L f n * spatialFourierCharacter n (L⁻¹ • y))
      (expandingTorusFunction a k L f (euclideanToTorus (L⁻¹ • y))) := by
  have h := (summable_expandingTorusTerm a k L ha ha1 hk hL f).hasSum.mapL
    (ContinuousMap.evalCLM (R := ℂ) (euclideanToTorus (L⁻¹ • y)))
  simpa [expandingTorusTerm, expandingTorusFunction, torusCharacter_euclidean] using h

theorem expandingPhysical_space_bound (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) (x y : E) :
    ‖expandingTorusFunction a (k + 2) L f (euclideanToTorus (L⁻¹ • x)) -
      expandingTorusFunction a (k + 2) L f (euclideanToTorus (L⁻¹ • y))‖ ≤
      expandingJetBound a k * ‖f‖ * ‖x - y‖ := by
  have hx := hasSum_expandingPhysical a (k + 2) L ha ha1 (by linarith) hL f x
  have hy := hasSum_expandingPhysical a (k + 2) L ha ha1 (by linarith) hL f y
  have hterm (n : frequencyLattice) :
      ‖expandingFourierCoefficient a (k + 2) L f n * spatialFourierCharacter n (L⁻¹ • x) -
        expandingFourierCoefficient a (k + 2) L f n * spatialFourierCharacter n (L⁻¹ • y)‖ ≤
      ((1 + (‖n‖ / L) ^ 2) * ‖expandingFourierCoefficient a (k + 2) L f n‖) * ‖x - y‖ := by
    rw [← mul_sub, norm_mul]
    have h := scaledFourierCharacter_lipschitz L (by linarith) n x y
    have hr : ‖n‖ / L ≤ 1 + (‖n‖ / L) ^ 2 := by nlinarith [sq_nonneg (‖n‖ / L - 1)]
    calc
      _ ≤ ‖expandingFourierCoefficient a (k + 2) L f n‖ * ((‖n‖ / L) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ ≤ ‖expandingFourierCoefficient a (k + 2) L f n‖ * ((1 + (‖n‖ / L) ^ 2) * ‖x - y‖) := by gcongr
      _ = _ := by ring
  apply le_of_tendsto (hx.sub hy).norm
  filter_upwards [] with S
  calc
    _ ≤ ∑ n ∈ S, ‖expandingFourierCoefficient a (k + 2) L f n * spatialFourierCharacter n (L⁻¹ • x) -
        expandingFourierCoefficient a (k + 2) L f n * spatialFourierCharacter n (L⁻¹ • y)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ((1 + (‖n‖ / L) ^ 2) * ‖expandingFourierCoefficient a (k + 2) L f n‖) * ‖x - y‖ :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = (∑ n ∈ S, (1 + (‖n‖ / L) ^ 2) * ‖expandingFourierCoefficient a (k + 2) L f n‖) * ‖x - y‖ :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_expandingFourier_jet_le a k L ha ha1 hk hL f S) (norm_nonneg _)

end DefocusingNLS

end OAI

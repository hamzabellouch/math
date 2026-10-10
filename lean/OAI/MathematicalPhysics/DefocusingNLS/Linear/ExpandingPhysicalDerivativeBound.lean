import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalModeRate
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFourierJetBound

namespace OAI

/-! # Radius-uniform bounds for finite physical Fourier time derivatives -/

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingPhysicalDerivative_sum_bound (a b k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f g : FourierL2) (y : E) (S : Finset frequencyLattice) :
    (∑ n ∈ S, ‖(physicalModeRate a b L n y * expandingFourierCoefficient a (k + 2) L f n +
      expandingFourierCoefficient a (k + 2) L g n) * spatialFourierCharacter n (L⁻¹ • y)‖) ≤
      (|a| + |b| + 1 + ‖y‖ / 2) * expandingJetBound a k * ‖f‖ +
        expandingEmbeddingBound a (k + 2) * ‖g‖ := by
  let K := |a| + |b| + 1 + ‖y‖ / 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht (n : frequencyLattice) :
      ‖(physicalModeRate a b L n y * expandingFourierCoefficient a (k + 2) L f n +
        expandingFourierCoefficient a (k + 2) L g n) * spatialFourierCharacter n (L⁻¹ • y)‖ ≤
      K * ((1 + (‖n‖ / L) ^ 2) * ‖expandingFourierCoefficient a (k + 2) L f n‖) +
        ‖expandingFourierCoefficient a (k + 2) L g n‖ := by
    rw [norm_mul, spatialFourierCharacter_norm, mul_one]
    calc
      _ ≤ ‖physicalModeRate a b L n y * expandingFourierCoefficient a (k + 2) L f n‖ +
          ‖expandingFourierCoefficient a (k + 2) L g n‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul]
        have h := mul_le_mul_of_nonneg_right
          (physicalModeRate_norm_le a b L (by linarith) n y)
          (norm_nonneg (expandingFourierCoefficient a (k + 2) L f n))
        dsimp only [K]
        nlinarith
  calc
    _ ≤ ∑ n ∈ S, (K * ((1 + (‖n‖ / L) ^ 2) * ‖expandingFourierCoefficient a (k + 2) L f n‖) +
        ‖expandingFourierCoefficient a (k + 2) L g n‖) := Finset.sum_le_sum (fun n _ => ht n)
    _ = K * (∑ n ∈ S, (1 + (‖n‖ / L) ^ 2) * ‖expandingFourierCoefficient a (k + 2) L f n‖) +
        ∑ n ∈ S, ‖expandingFourierCoefficient a (k + 2) L g n‖ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ K * (expandingJetBound a k * ‖f‖) + expandingEmbeddingBound a (k + 2) * ‖g‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (sum_expandingFourier_jet_le a k L ha ha1 hk hL f S) hK
      · exact ((summable_norm_expandingFourierCoefficient a (k + 2) L ha ha1 (by linarith) hL g).sum_le_tsum
          S (fun n _ => norm_nonneg _)).trans
          (tsum_norm_expandingFourierCoefficient_le a (k + 2) L ha ha1 (by linarith) hL g)
    _ = _ := by ring

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFourierTest
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalCharacter
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeDuality

namespace OAI

/-! # The expanding-torus free step has the same Schwartz dual action as the whole-space group -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingFreeTime_phase (L t : ℝ) (hL : 0 < L) (n : frequencyLattice) :
    schrodingerMultiplier (expandingFreeTime L t) n =
      homogeneousSchrodingerPhase (1 - Real.exp (-t)) (L⁻¹ • (n : E)) := by
  have hpow : L ^ (-2 : ℝ) = (L⁻¹) ^ 2 := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by ring, Real.rpow_neg hL.le,
      Real.rpow_two, inv_pow]
  unfold schrodingerMultiplier homogeneousSchrodingerPhase expandingFreeTime
  rw [hpow, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
  congr 1
  change -Complex.I * (((L⁻¹) ^ 2 * (1 - Real.exp (-t)) * ‖n‖ ^ 2 : ℝ) : ℂ) =
    (((-(1 - Real.exp (-t)) * (L⁻¹ * ‖n‖) ^ 2 : ℝ)) : ℂ) * Complex.I
  push_cast
  ring

theorem expandingFreeStep_fourier_duality (a b k L t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (φ : 𝓢(E, ℂ)) (f : FourierL2) :
    expandingFourierTest a k (expandingRadius L t) ha ha1 hk
        (hL.trans (expandingRadius_ge L t hL ht)) φ
        (expandingFreeStep a b k L t ha hk hL ht f) =
      expandingFourierTest a k L ha ha1 hk hL (homogeneousFreeDualTest a b t φ) f := by
  simp only [expandingFourierTest_apply]
  apply tsum_congr
  intro n
  rw [expandingFreeStep_coefficient, homogeneousFreeDualTest_apply,
    ← expandingFreeTime_phase L t (lt_of_lt_of_le zero_lt_one hL) n]
  have he : Real.exp (-t / 2) • (L⁻¹ • (n : E)) =
      (expandingRadius L t)⁻¹ • (n : E) := by
    rw [smul_smul, expandingRadius_inv, mul_comm]
  rw [he]
  change expandingFreeAmplitude a b t * _ * _ * _ =
    _ * (expandingFreeAmplitude a b t * _ * _)
  ring

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeightedObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEnergyInterpolation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEnergyComponents
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYProduct
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalInjective

namespace OAI

/-! # The compact low-energy part of a Schwartz coefficient

On the dense physical Schwartz domain, multiplication by a fixed Schwartz
coefficient takes bounded weakly null data to zero in the exact low energy.
The proof combines physical L² observation, Plancherel and frequency splitting.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousYProduct_physicalSchwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (V f : 𝓢(E, ℂ)) :
    homogeneousYProduct a k ha ha1 hk
      (homogeneousSchwartzEmbedding a k ha ha1 hk V)
      (homogeneousSchwartzEmbedding a k ha ha1 hk f) =
    homogeneousSchwartzEmbedding a k ha ha1 hk (SchwartzMap.smulLeftCLM ℂ V f) := by
  apply homogeneousPhysicalCLM_injective a k ha ha1 hk
  apply DFunLike.ext
  intro x
  rw [homogeneousYProduct_physical, homogeneousPhysicalCLM_Schwartz,
    homogeneousPhysicalCLM_Schwartz, homogeneousPhysicalCLM_Schwartz,
    SchwartzMap.smulLeftCLM_apply_apply V.hasTemperateGrowth]
  rfl

private theorem schwartz_frequency_integrable (s : ℝ) (hs : 0 ≤ s) (f : 𝓢(E, ℂ)) :
    Integrable (fun ξ : E => ‖ξ‖ ^ (2 * s) * ‖radianFourierKernel f ξ‖ ^ 2) := by
  have h := homogeneousFourierMagnitude_sq_integrable s hs (radianFourierKernel f)
  convert h using 1
  funext ξ
  simp only [homogeneousFourierMagnitude, mul_pow]
  rw [← Real.rpow_natCast (‖ξ‖ ^ s) 2, ← Real.rpow_mul (norm_nonneg _)]
  congr 2
  ring

theorem homogeneousLowEnergy_schwartz_interpolation (a k ε : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hε : 0 < ε) (V : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(E, ℂ),
      ‖homogeneousLowEnergy a k ha1 hk
        (homogeneousYProduct a k ha ha1 hk
          (homogeneousSchwartzEmbedding a k ha ha1 hk V)
          (homogeneousSchwartzEmbedding a k ha ha1 hk f))‖ ^ 2 ≤
      ε * ‖homogeneousYProduct a k ha ha1 hk
          (homogeneousSchwartzEmbedding a k ha ha1 hk V)
          (homogeneousSchwartzEmbedding a k ha ha1 hk f)‖ ^ 2 +
        C * ‖homogeneousWeightedObservation a k ha ha1 hk V (V.memLp 2)
          (homogeneousSchwartzEmbedding a k ha ha1 hk f)‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := homogeneousLowEnergy_interpolation a k ε ha ha1 hk hε
  refine ⟨C, hC, fun f => ?_⟩
  let P : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM ℂ V f
  let v := homogeneousSchwartzEmbedding a k ha ha1 hk P
  have hp : homogeneousYProduct a k ha ha1 hk
      (homogeneousSchwartzEmbedding a k ha ha1 hk V)
      (homogeneousSchwartzEmbedding a k ha ha1 hk f) = v :=
    homogeneousYProduct_physicalSchwartz a k ha ha1 hk V f
  let c := ((2 * Real.pi) ^ (12 : ℕ))⁻¹
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hz : c * homogeneousFrequencyEnergy 0 (radianFourierKernel P) =
      ‖homogeneousWeightedObservation a k ha ha1 hk V (V.memLp 2)
        (homogeneousSchwartzEmbedding a k ha ha1 hk f)‖ ^ 2 := by
    rw [radianFourier_energy_zero, homogeneousWeightedObservation_norm_sq,
      ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    unfold homogeneousFrequencyEnergy
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [mul_zero, Real.rpow_zero, one_mul,
      homogeneousPhysicalCLM_Schwartz, P,
      SchwartzMap.smulLeftCLM_apply_apply V.hasTemperateGrowth, smul_eq_mul]
  have hl : c * homogeneousFrequencyEnergy (6 - a) (radianFourierKernel P) =
      ‖homogeneousLowEnergy a k ha1 hk v‖ ^ 2 :=
    (homogeneousLowEnergy_Schwartz_norm_sq a k ha ha1 hk _).symm
  have hh : c * homogeneousFrequencyEnergy k (radianFourierKernel P) =
      ‖homogeneousHighEnergy a k ha1 hk v‖ ^ 2 :=
    (homogeneousHighEnergy_Schwartz_norm_sq a k ha ha1 hk _).symm
  have hhigh := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg v)).mpr
    (homogeneousHighEnergy_norm_le a k ha1 hk v)
  have hi := mul_le_mul_of_nonneg_left
    (hc (radianFourierKernel P)
      (by simpa only [mul_zero, Real.rpow_zero, one_mul] using schwartz_frequency_integrable 0 le_rfl P)
      (schwartz_frequency_integrable k (by linarith) P)) hc0.le
  rw [mul_add, mul_left_comm c ε, hl, hh, mul_left_comm c C, hz] at hi
  rw [hp]
  nlinarith


end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactLowCommutator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProductSmoothRemainder
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.UniformCutoffLimit

namespace OAI

/-! # Strong compactness of sampled compact-coefficient commutators -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_expandingSample_commutator (a M R : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ))
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a (N + 1 : ℕ) (L n) (f n)
        (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (K : 𝓢(E, ℂ)) (hK : ∀ y : E, R < ‖y‖ → K y = 0)
    (j : Fin (N + 1) → Fin 12) :
    Tendsto (fun n => expandingProductCommutator a (L n) (N + 1) ha ha1 hN (hL n) j
      (schwartzTorusSample a (N + 1 : ℕ) (L n) ha1 hN (hL n) (radianFourierKernel K)) (f n))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hc⟩ := exists_expandingProductCommutator_smooth_remainder a N ha ha1 hN
    (radianFourierKernel K)
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hf 0)
  let q := fun n => schwartzTorusSample a (N + 1 : ℕ) (L n) ha1 hN (hL n) (radianFourierKernel K)
  apply tendsto_zero_of_uniform_cutoff
    (fun n => expandingProductCommutator a (L n) (N + 1) ha ha1 hN (hL n) j (q n) (f n))
    (fun S hS n => expandingProductCommutator a (L n) (N + 1) ha ha1 hN (hL n) j (q n)
      (expandingSmoothLow (L n) S (by linarith) (f n))) (C * M) (mul_nonneg hC hM)
  · intro S hS
    exact tendsto_expandingSample_low_commutator a M R S (N + 1) ha ha1 hN (by linarith)
      L hL hLinf f hf hlocal K hK j
  · intro S hS n
    calc
      _ ≤ (C / S) * ‖f n‖ := hc (L n) S (hL n) hS (f n) j
      _ ≤ (C / S) * M := mul_le_mul_of_nonneg_left (hf n) (div_nonneg hC (by linarith))
      _ = (C * M) / S := by ring

end DefocusingNLS

end OAI

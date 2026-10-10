import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLowMassLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCompactMassLimit

namespace OAI

/-! # Compact lower-order product for the actual unfiltered field -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_expandingSample_lowEnergy_product (a M R : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ))
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a N (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
    (K : 𝓢(E, ℂ)) (hK : ∀ y : E, R < ‖y‖ → K y = 0) :
    Tendsto (fun n => expandingLowEnergy a N (L n) (hL n)
      (expandingProduct a N (L n) ha ha1 hN (hL n)
        (schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel K)) (f n)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hc⟩ := exists_schwartzTorusSample_norm_bound a N ha1 hN (radianFourierKernel K)
  let A : ℝ := 2 * Real.sqrt (4 ^ (N : ℝ)) * expandingEmbeddingBound a N
  have hA : 0 ≤ A := by dsimp [A]; unfold expandingEmbeddingBound; positivity
  let g := fun n => expandingProduct a N (L n) ha ha1 hN (hL n)
    (schwartzTorusSample a N (L n) ha1 hN (hL n) (radianFourierKernel K)) (f n)
  have hg (n : ℕ) : ‖g n‖ ≤ A * C * M :=
    (expandingProduct_norm_le a N (L n) ha ha1 hN (hL n) _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (hc (L n) (hL n)) hA)
        (hf n) (norm_nonneg _) (mul_nonneg hA hC))
  exact tendsto_expandingLowEnergy_of_mass a (A * C * M) N ha ha1 hN L hL g hg
    (tendsto_expandingSample_product_mass a N M R ha ha1 hN L hL hLinf f hf hlocal K hK)

end DefocusingNLS

end OAI

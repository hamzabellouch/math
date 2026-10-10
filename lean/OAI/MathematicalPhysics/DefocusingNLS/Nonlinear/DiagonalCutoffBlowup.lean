import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalCutoffStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStableBlowup

namespace OAI

/-! # Blowup data from finite diagonal stable coordinates -/

open Set Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] diagonalRealCoordinates

theorem exists_diagonalCutoff_blowup {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (ham : 2 * a * m = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ y : E, ‖y‖ < 1 / 2 → χ y = 1)
    (hχzero : ∀ y : E, 2 < ‖y‖ → χ y = 0)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (hQzero : Qp 0 ≠ 0)
    (π : HomogeneousY a k →L[ℝ] V)
    (hstable : HasFiniteDiagonalCutoffStableOrbits a b k ha ha1 hk m
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp π) :
    ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 → ∃ f : FourierL2,
      BddAbove (maximalSobolevInteractionDomain k (by linarith) m f) ∧
      sSup (maximalSobolevInteractionDomain k (by linarith) m f) = L.1 ^ (-2 : ℝ) ∧
      Tendsto (fun t => (L.1 ^ (-2 : ℝ) - t) ^ a *
        ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k (by linarith) m f t) 0‖)
        (𝓝[<] (L.1 ^ (-2 : ℝ))) (𝓝 ‖Qp 0‖) := by
  obtain ⟨G, hspan, hspec, horbit⟩ := hstable
  obtain ⟨ρ, hρ, L₀, hL₀⟩ := exists_cutoffStable_blowup a b k ha ha1 hk m ham
    χ hχ hχone hχzero Qp hQp hQzero horbit
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨ζ, π, _, hw⟩ := hL₀ L hL
  obtain ⟨f, _, hf⟩ := hw 0 (by simpa using (by positivity : (0 : ℝ) ≤ ρ / 4)) (map_zero π)
  exact ⟨f, hf⟩

end DefocusingNLS

end OAI

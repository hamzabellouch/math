import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalStartingData

namespace OAI

/-! # A physical initial datum admitting the constructed global similarity orbit -/

open Set Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

def HasPhysicalCutoffOrbit (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (f : FourierL2) : Prop :=
  ∃ (L : Radius) (θ : ℝ) (x : SchrodingerTorus) (u : ℝ → FourierL2),
    ∃ hu : ContinuousOn u (Ici 0),
      u 0 = physicalStartingOperator a k ha hk L θ x f ∧
      (∀ (S : ℝ) (hS : 0 < S), expandingSlabRestriction u hu S =
        expandingPicard a b k L.1 S ha hk L.2 hS.le
          (expandingNonlinearReaction a k L.1 S ha ha1 hk L.2 m) (u 0)
          (expandingSlabRestriction u hu S)) ∧
      Tendsto (fun s => ‖u s - sampledCutoffProfileOrbit a k L.1 ha1 hk L.2 χ hχ Q hQ s‖)
        atTop (𝓝 0)

end DefocusingNLS

end OAI

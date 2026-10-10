import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEscapedEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SpacetimeStableObservation

namespace OAI

/-! # Escaped torus energy controlled by decay of its identified limit -/

open Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingProfile_stable_limit_energy (a b k T Q M c C R A η : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hc : 0 ≤ c) (hC : 0 ≤ C) (m : ℕ)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (q : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ n s, ‖q n s‖ ≤ Q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (henergy : ∀ n (s : Icc (0 : ℝ) T) (w : FourierL2),
      let l := expandingRadiusCurve (L n) T (hL n) s;
      -a * ‖expandingLowEnergy a k l.1 l.2 w‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k l.1 l.2 w‖ ^ 2 +
        2 * inner ℝ w (expandingLinearizedPotential a k l.1 ha ha1 hk l.2 m (q n s) w) ≤
      -c * ‖w‖ ^ 2 + C * ‖expandingPhysicalBall a k l.1 R ha ha1 hk l.2 w‖ ^ 2)
    (v : C(Icc (0 : ℝ) T × E, ℂ))
    (w : Icc (0 : ℝ) T → HomogeneousY a k)
    (hw : ∀ t y, v (t, y) = homogeneousPhysicalCLM a k ha ha1 hk (w t) y)
    (hA : 0 ≤ A) (hdecay : ∀ t, ‖w t‖ ≤ A * Real.exp (-η * (t : ℝ)))
    (hv : Tendsto (fun n => expandingSpacetimePath a k (L n) T ha ha1 hk (hL n)
      (expandingProfileTrajectory a b k (L n) T ha ha1 hk (hL n) hT m Q hQ (q n) (hq n) (f n)))
      atTop (𝓝 v)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ‖expandingProfileTrajectory a b k (L n) T ha ha1 hk (hL n) hT m Q hQ (q n) (hq n)
        (f n) ⟨T, hT, le_rfl⟩‖ ^ 2 ≤ Real.exp (-c * T) * M ^ 2 +
        (C * (‖homogeneousPhysicalCLM a k ha ha1 hk‖ * A) ^ 2) *
          observationDecayIntegral c (2 * η) T + ε := by
  have hi := spacetime_stable_observation_integral_le a k T R C A η ha ha1 hk hT
    hC hA c v w hw hdecay
  intro ε hε
  filter_upwards [expandingProfile_escaped_energy a b k T Q M c C R ha ha1 hk hT
    hQ hM hc hC m L hL q hq f hf henergy v hv ε hε] with n hn
  apply hn.trans
  linarith

end DefocusingNLS

end OAI

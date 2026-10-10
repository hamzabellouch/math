import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfilePropagator

namespace OAI

/-! # Initial value of the constructed expanding-torus propagator -/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingProfileTrajectory

theorem expandingProfileTrajectory_initial (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (q : C(Icc (0 : ℝ) T, FourierL2))
    (hq : ∀ t, ‖q t‖ ≤ Q) (f : FourierL2) :
    expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ q hq f ⟨0, le_rfl, hT⟩ = f := by
  rw [expandingProfileTrajectory_eq]
  simp [expandingDuhamel]

end DefocusingNLS

end OAI

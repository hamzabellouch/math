import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSpacetimeObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileTimeEquicontinuity

namespace OAI

/-! # The actual linearized trajectory in physical space-time coordinates -/

open Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] expandingProfileTrajectory expandingTorusFunction expandingSpacetimePath

noncomputable def expandingProfilePhysicalPath (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (q : C(Icc (0 : ℝ) T, FourierL2))
    (hq : ∀ t, ‖q t‖ ≤ Q) (f : FourierL2) : C(Icc (0 : ℝ) T × E, ℂ) :=
  expandingSpacetimePath a k L T ha ha1 hk hL
    (expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ q hq f)

end DefocusingNLS

end OAI

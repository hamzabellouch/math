import OAI.Analysis.KadisonKastler.CenterAlgebra
import OAI.Analysis.KadisonKastler.UnitaryApproximation

namespace OAI

/-! # The published Dixmier averaging input

Only the contraction case is retained. Blackadar, *Operator Algebras*,
Definition III.2.5.16 and Theorem III.2.5.18, p. 282 (PDF p. 290), state that
the norm-closed convex hull of the unitary conjugates of an element of a
von Neumann algebra meets its center. This input contains no comparison
between different algebras and no perturbation bound.

Primary text: https://bruceblackadar.com/Mathematics/Cycr.pdf
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def innerUnitaryOrbit (N : VonNeumannAlgebra H) (x : H →L[ℂ] H) :
    Set (H →L[ℂ] H) :=
  Set.range (fun u : unitary (Algebra N) => unitaryConj (ambientAlgebraUnitary u) x)

/-- The published averaging statement used to identify centers. -/
def PublishedDixmierAveraging (N : VonNeumannAlgebra H) : Prop :=
  ∀ x ∈ unitBall N, ∃ z ∈ concreteCenter N,
    z ∈ closure (convexHull ℝ (innerUnitaryOrbit N x))

/-- The closed convex hull stays in every closed norm ball containing the
orbit. This supplies both bounds needed after Dixmier averaging. -/
theorem norm_sub_le_of_closed_convex_orbit
    (N : VonNeumannAlgebra H) (x c z : H →L[ℂ] H) (r : ℝ)
    (h : ∀ u : unitary (Algebra N), ‖unitaryConj (ambientAlgebraUnitary u) x - c‖ ≤ r)
    (hz : z ∈ closure (convexHull ℝ (innerUnitaryOrbit N x))) : ‖z - c‖ ≤ r := by
  have hs : innerUnitaryOrbit N x ⊆ Metric.closedBall c r := by
    rintro _ ⟨u, rfl⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm] using h u
  simpa only [Metric.mem_closedBall, dist_eq_norm] using
    closure_minimal (convexHull_min hs (convex_closedBall c r)) Metric.isClosed_closedBall hz

theorem norm_le_of_closed_convex_orbit
    (N : VonNeumannAlgebra H) (x z : H →L[ℂ] H) (hx : ‖x‖ ≤ 1)
    (hz : z ∈ closure (convexHull ℝ (innerUnitaryOrbit N x))) : ‖z‖ ≤ 1 := by
  simpa only [sub_zero] using norm_sub_le_of_closed_convex_orbit N x 0 z 1
    (fun u => by simpa only [sub_zero, norm_unitaryConj] using hx) hz

end

end KadisonKastler

end OAI

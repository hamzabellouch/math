import OAI.MeasureTheory.Falconer.Geometry.IntegerRectangle
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-!
# The exact finite lattice projection input for general-dimensional tube counting

Loomis–Whitney, *An inequality related to the isoperimetric inequality*,
Bull. AMS 55 (1949), 961–962, DOI 10.1090/S0002-9904-1949-09320-5.
The finite lattice consequence is stated explicitly in Balister–Bollobás,
*Projections, entropy and sumsets*, Combinatorica 32 (2012), equation (7),
specialized here to the (n+1) coordinate-deletion projections, an n-uniform cover.
Author manuscript: https://www.memphis.edu/msci/people/pbalistr/projections.pdf
Only this counting specialization is an explicit conditional input.
-/

namespace Falconer
open scoped BigOperators

abbrev dropGridCoordinate {n : ℕ} (i : Fin (n+1)) (z : Fin (n+1) → ℤ) : Fin n → ℤ :=
  fun j => z (i.succAbove j)

def PublishedFiniteLoomisWhitney : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ S : Finset (Fin (n+1) → ℤ),
    S.card^n ≤ ∏ i : Fin (n+1), (S.image (dropGridCoordinate i)).card

end Falconer

end OAI

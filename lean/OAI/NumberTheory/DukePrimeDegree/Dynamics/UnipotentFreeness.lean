import OAI.NumberTheory.DukePrimeDegree.Geometry.PositiveRootPattern
import OAI.NumberTheory.DukePrimeDegree.Dynamics.GenericLatticeStabilizer

namespace OAI

/-!
# Freeness of the full positive unipotent action

At the generic lattices already supplied by diagonal recurrence, no
nonzero lattice vector has a zero coordinate. A stabilizer element with
one identity column must therefore fix every lattice vector, so is the
identity. In particular all positive-root groups act freely there,
simultaneously.
-/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem positiveRootPattern_stabilizer_trivial {d : ℕ}
    (x : X (d + 1)) (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (S : Finset (Fin (d + 1) × Fin (d + 1))) (hpos : ∀ p ∈ S, p.1 < p.2)
    (g : G (d + 1)) (hg : PositiveRootPattern S g) (hfix : rightAction x g = x) :
    g = 1 := by
  apply stabilizer_trivial_of_identity_column x hx g hfix 0
  intro r
  apply hg r 0
  intro h
  exact (Fin.not_lt_zero r) (hpos (r, 0) h)

theorem ae_positiveRootPattern_stabilizer_trivial
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ (S : Finset (Fin (d + 1) × Fin (d + 1))),
      (∀ p ∈ S, p.1 < p.2) → ∀ g : G (d + 1),
        PositiveRootPattern S g → rightAction x g = x → g = 1 := by
  filter_upwards [ae_no_coordinate_zero d μ hA] with x hx S hpos g hg hfix
  exact positiveRootPattern_stabilizer_trivial x hx S hpos g hg hfix

end DukePrimeDegree

end

end OAI

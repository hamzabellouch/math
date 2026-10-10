import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialSpatial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListOutputBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListBoundProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedPortChain

namespace OAI

/-! Size and coefficient bounds for the same full spatial graph that is routed
to the lattice. Active-star bonds and the scalar offset are included. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList.SpatialInput
open scoped Classical
variable {rows width A D : ℕ} (I : SpatialInput rows width A D)

theorem model_size : I.model.n+Fintype.card I.model.Term ≤
    I.n+5*I.bonds.length+12*D*I.bonds.length := by
  have hn := initial_iterate_count_le I.n I.bonds I.bounded I.constant I.precision D
  have he := initial_iterate_bonds_le I.n I.bonds I.bounded I.constant I.precision D
  change I.state.1+Fintype.card (Fin (fullList I.state).length) ≤ _
  rw [Fintype.card_fin]
  calc
    _ ≤ (I.n+2*I.bonds.length+4*D*I.bonds.length)+
        (3*I.bonds.length+8*D*I.bonds.length) := Nat.add_le_add hn he
    _ = _ := by ring

theorem model_coefficientBound {L T : ℝ} (hN : 0 ≤ I.precision)
    (hL : 1 ≤ L) (hT : |(I.precision:ℝ)| ≤ T)
    (hc : |(I.constant:ℝ)| ≤ L) (hw : ∀ b ∈ I.bonds, |(b.2.2:ℝ)| ≤ L) :
    I.model.exchangeGraph.CoefficientBound (outputCoefficient I.bonds.length D L T) := by
  have h := initial_iterate_coefficientBound I.n I.bonds I.bounded I.constant I.precision
    hN hL hT hc hw D
  constructor
  · exact h.scalar
  · intro e
    exact h.full I.state ((fullList I.state).get e) (List.get_mem _ e)

theorem model_nat_coefficientBound {L T : ℕ} (hN : 0 ≤ I.precision)
    (hL : 1 ≤ L) (hT : |(I.precision:ℝ)| ≤ T)
    (hc : |(I.constant:ℝ)| ≤ L) (hw : ∀ b ∈ I.bonds, |(b.2.2:ℝ)| ≤ L) :
    I.model.exchangeGraph.CoefficientBound
      (outputCoefficientNat I.bonds.length D L T) := by
  rw [outputCoefficientNat_cast]
  exact I.model_coefficientBound hN (by exact_mod_cast hL) hT hc hw

end ContinuumCoulomb.QuantumForkList.SpatialInput

end

end OAI

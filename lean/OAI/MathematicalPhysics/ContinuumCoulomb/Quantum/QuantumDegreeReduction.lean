import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkInitialMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkInitialSize

namespace OAI

/-! The bounded-degree exchange reduction with actual full-space energy and size bounds. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

def qmaDegreeReduction {n m : ℕ} (left right : Fin m → Fin n) (J : Fin m → ℝ)
    (constant N : ℝ) (D : ℕ) : QMAWeightedForkNetwork n :=
  let A := 3*∑ e, (1+2*|J e|)
  let B := |constant|+4*∑ e, (1+|J e|)^2
  (qmaSubdivisionWeighted left right J constant (qmaRoutingScale A B N)).iterate N D

theorem qmaDegreeReduction_graph {n m : ℕ} (left right : Fin m → Fin n) (J : Fin m → ℝ)
    (constant N : ℝ) (D : ℕ) :
    (qmaDegreeReduction left right J constant N D).graph =
      (qmaSubdivisionNetwork left right).iterate D := by
  unfold qmaDegreeReduction
  rw [QMAWeightedForkNetwork.iterate_graph]
  rfl

theorem qmaDegreeReduction_degree {n m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ e, left e ≠ right e) (J : Fin m → ℝ) (constant N : ℝ) (D : ℕ)
    (hD : ∀ i, qmaGraphDegree left right i ≤ D) :
    ∀ v, qmaGraphDegree (qmaDegreeReduction left right J constant N D).graph.state.fullLeft
      (qmaDegreeReduction left right J constant N D).graph.state.fullRight v ≤ 3 := by
  rw [qmaDegreeReduction_graph]
  exact qmaSubdivision_degree_three left right hneq D hD

theorem qmaDegreeReduction_vertices {n m : ℕ} (left right : Fin m → Fin n) (J : Fin m → ℝ)
    (constant N : ℝ) (D : ℕ) :
    (qmaDegreeReduction left right J constant N D).graph.n ≤ n+2*m+4*D*m := by
  rw [qmaDegreeReduction_graph]
  exact qmaSubdivision_vertices left right D

theorem qmaDegreeReduction_edges {n m : ℕ} (left right : Fin m → Fin n) (J : Fin m → ℝ)
    (constant N : ℝ) (D : ℕ) :
    let G := (qmaDegreeReduction left right J constant N D).graph
    Fintype.card (G.Edge ⊕ (Σ i, Fin (G.degree i))) ≤ 3*m+8*D*m := by
  dsimp only
  rw [qmaDegreeReduction_graph]
  exact qmaSubdivision_edges left right D

theorem qmaDegreeReduction_energy {n m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ e, left e ≠ right e) (J : Fin m → ℝ) (constant : ℝ)
    {N : ℝ} (hN : 0 < N) (D : ℕ) :
    |(qmaDegreeReduction left right J constant N D).energy -
      sourceMatrixBottom n (qmaExchangeMatrix left right J constant)| ≤ ((D:ℝ)+1)/N := by
  let A := 3*∑ e, (1+2*|J e|)
  let B := |constant|+4*∑ e, (1+|J e|)^2
  let G := qmaSubdivisionWeighted left right J constant (qmaRoutingScale A B N)
  have h0 := qmaSubdivision_energy_error left right hneq J constant hN
  have hi := G.iterate_energy_error hN D
  change |(G.iterate N D).energy-sourceMatrixBottom n (qmaExchangeMatrix left right J constant)| ≤ _
  calc
    _ ≤ |(G.iterate N D).energy-G.energy| +
        |G.energy-sourceMatrixBottom n (qmaExchangeMatrix left right J constant)| := abs_sub_le _ _ _
    _ ≤ (D:ℝ)/N+1/N := add_le_add hi h0
    _ = ((D:ℝ)+1)/N := by ring

end ContinuumCoulomb

end

end OAI

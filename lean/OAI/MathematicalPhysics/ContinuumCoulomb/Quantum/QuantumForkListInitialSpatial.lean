import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListSpatialPackage
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrdinalSpatial

namespace OAI

/-! A bounded-density local input list yields the actual degree-three
spatial output, with its full Hamiltonian and fixed density constant. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

def spatialDensity (A D : ℕ) : ℕ := ((1+2*D)^D*(D+1))*A

structure SpatialInput (rows width A D : ℕ) where
  n : ℕ
  bonds : List Bond
  constant : ℚ
  precision : ℚ
  cell : ℕ → QMAGridCell rows width
  bounded : SourceBondLists.bounded n bonds
  noLoops : ∀ b ∈ bonds, b.1≠b.2.1
  degree : ∀ v : Fin n, QuantumForkList.degree bonds v.val ≤ D
  density : ∀ p, qmaCellMass (fun v : Fin n => cell v.val) p ≤ A
  locality : BondLocal bonds cell CommonCell

namespace SpatialInput
variable {rows width A D : ℕ} (I : SpatialInput rows width A D)

def state : State := iterate I.precision D (initial I.n I.bonds I.constant I.precision)

def cells : ℕ → QMAGridCell rows width :=
  iterateCell I.precision D (initial I.n I.bonds I.constant I.precision)
    (initialCell I.n I.bonds I.cell)

theorem validPorts : ValidPorts I.state.1 I.state.2.2.2 :=
  iterate_validPorts _ _ (initial_validPorts _ _ _ _) _

theorem state_bounded : SourceBondLists.bounded I.state.1 I.state.2.1 :=
  iterate_ordinary_bounded _ _ (initial_validPorts _ _ _ _) (initial_ordinary_bounded _ _ _ _) _

theorem state_noLoops : ∀ b ∈ I.state.2.1, b.1≠b.2.1 :=
  iterate_ordinary_noLoops _ _ (initial_validPorts _ _ _ _) (initial_ordinary_noLoops _ _ _ _) _

theorem state_density (p : QMAGridCell rows width) :
    qmaCellMass (fun v : Fin I.state.1 => I.cells v.val) p ≤ spatialDensity A D := by
  have h := initial_iterate_cell_mass_le I.n I.bonds I.bounded I.noLoops
    I.constant I.precision I.cell D I.degree D p
  exact h.trans (Nat.mul_le_mul_left _ (I.density p))

theorem state_degree (v : Fin I.state.1) : QuantumForkList.degree (fullList I.state) v.val ≤ 3 :=
  initial_iterate_full_degree_of_bound I.n I.bonds I.noLoops I.constant I.precision D I.degree v

theorem state_locality : BondLocal (fullList I.state) I.cells CommonCell :=
  initial_iterate_full_cellLocal I.n I.bonds I.constant I.precision I.cell CommonCell
    commonCell_refl I.locality D

def model : QMASpatialExchangeModel (spatialDensity A D) (27*spatialDensity A D) :=
  (spatialModel I.state I.validPorts I.state_bounded I.state_noLoops I.cells (spatialDensity A D)
    I.state_density I.state_degree I.state_locality).withOrdinalSlots (Equiv.refl _)

theorem model_n : I.model.n=I.state.1 := rfl

theorem model_rows : I.model.rows=rows := rfl

theorem model_width : I.model.width=width := rfl

theorem model_ordinal : I.model.withOrdinalSlots (Equiv.refl _) = I.model := rfl

theorem model_energy : I.model.energy=MediatorGraph.normalizedBottom (matrix I.state) :=
  congrArg MediatorGraph.normalizedBottom
    (spatialModel_matrix I.state I.validPorts I.state_bounded I.state_noLoops I.cells
      (spatialDensity A D) I.state_density I.state_degree I.state_locality)

theorem model_degree (v : Fin I.model.n) :
    qmaGraphDegree I.model.left I.model.right v ≤ 3 := by
  exact (degree_eq_graph I.state.1 (fullList I.state)
    (fullList_bounded I.state I.validPorts I.state_bounded) v) ▸ I.state_degree v

end SpatialInput
end ContinuumCoulomb.QuantumForkList

end

end OAI

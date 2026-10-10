import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListFullCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridMidpoint
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalSpatialPackage

namespace OAI

/-! Package the literal full fork graph with deterministic midpoint anchors.
The package keeps its actual spin indices, coefficients and scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped Classical

def fullList (s : State) : List Bond := s.2.1++activeBonds s.2.2.2

theorem fullList_bounded (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) : SourceBondLists.bounded s.1 (fullList s) := by
  intro b hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hb b hm
  · exact ⟨(activeBonds_valid hs b hm).1,(activeBonds_valid hs b hm).2.1⟩

theorem fullList_noLoops (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) : ∀ b ∈ fullList s, b.1≠b.2.1 := by
  intro b hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hn b hm
  · exact (activeBonds_valid hs b hm).2.2

def fullGraph (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) :=
  QuantumListGraph.ofBonds s.1 (fullList s) s.2.2.1
    (fullList_bounded s hs hb) (fullList_noLoops s hs hn)

theorem fullGraph_matrix (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) :
    qmaExchangeMatrix (fullGraph s hs hb hn).left (fullGraph s hs hb hn).right
      (fun e => ((fullGraph s hs hb hn).weight e:ℝ)) s.2.2.1 = matrix s := by
  change _ = QuantumRawExchange.rawMatrix s.1 (fullList s,s.2.2.1)
  rw [rawMatrix_eq_matrix]
  exact QuantumListGraph.ofBonds_matrix _ _ _ _ _

def CommonCell {rows width : ℕ} (p q : QMAGridCell rows width) : Prop :=
  ∃ a, QMAGridCellsNear p a ∧ QMAGridCellsNear q a

theorem commonCell_refl {rows width : ℕ} (p : QMAGridCell rows width) : CommonCell p p :=
  ⟨p,qmaGridCellsNear_refl p,qmaGridCellsNear_refl p⟩

def spatialModel {rows width : ℕ} (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hn : ∀ b ∈ s.2.1, b.1≠b.2.1)
    (cell : ℕ → QMAGridCell rows width) (A : ℕ)
    (hc : ∀ p, qmaCellMass (fun v : Fin s.1 => cell v.val) p ≤ A)
    (hd : ∀ v : Fin s.1, degree (fullList s) v.val ≤ 3)
    (hl : BondLocal (fullList s) cell CommonCell) : QMASpatialExchangeModel A (27*A) := by
  let G := fullGraph s hs hb hn
  let cells : Fin s.1 → QMAGridCell rows width := fun v => cell v.val
  let anchors := fun e => qmaGridMidpoint (cells (G.left e)) (cells (G.right e))
  have hg : ∀ e, QMAGridCellsNear (cells (G.left e)) (anchors e) ∧
      QMAGridCellsNear (cells (G.right e)) (anchors e) := by
    intro e
    obtain ⟨a,ha,hb⟩ := hl ((fullList s).get e) (List.get_mem _ e)
    exact qmaGridMidpoint_near _ _ a ha hb
  have hc' : ∀ p, (Finset.univ.filter (fun v => cells v=p)).card ≤ A := by
    intro p
    simpa only [qmaCellMass,Finset.card_filter] using hc p
  have hd' : ∀ v : Fin s.1, qmaGraphDegree G.left G.right v ≤ 3 := by
    intro v
    change qmaGraphDegree (SourceBondLists.bonds s.1 (fullList s)
      (fullList_bounded s hs hb)).left (SourceBondLists.bonds s.1 (fullList s)
      (fullList_bounded s hs hb)).right v ≤ 3
    exact (degree_eq_graph s.1 (fullList s) (fullList_bounded s hs hb) v) ▸ hd v
  exact qmaDegreeThreeSpatialModel G.left G.right G.distinct G.weight s.2.2.1
    cells anchors hc' hd' hg

theorem spatialModel_matrix {rows width : ℕ} (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hn : ∀ b ∈ s.2.1, b.1≠b.2.1)
    (cell : ℕ → QMAGridCell rows width) (A : ℕ)
    (hc : ∀ p, qmaCellMass (fun v : Fin s.1 => cell v.val) p ≤ A)
    (hd : ∀ v : Fin s.1, degree (fullList s) v.val ≤ 3)
    (hl : BondLocal (fullList s) cell CommonCell) :
    let M := spatialModel s hs hb hn cell A hc hd hl
    qmaExchangeMatrix M.left M.right (fun e => (M.weight e:ℝ)) M.constant = matrix s :=
  fullGraph_matrix s hs hb hn

end ContinuumCoulomb.QuantumForkList

end

end OAI

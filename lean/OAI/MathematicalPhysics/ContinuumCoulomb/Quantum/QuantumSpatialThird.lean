import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialSubdivision
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalThirdSupported

namespace OAI

/-! The third-order gadget preserves the grid and bounded spatial density. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem QMASpatialModel.third {A B : ℕ} (M : QMASpatialModel 3 A B)
    {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMASpatialModel 2 (A+4^3*B) (7*4^3*B),
      |G.toQMARealLocalModel.energy-M.toQMARealLocalModel.energy| ≤ 1/N ∧
      G.rows = M.rows ∧ G.width = M.width := by
  obtain ⟨F,hFH,hFR,hFS,hFE⟩ := qmaLocalThird_supported M.matrix M.sites M.card
    M.localOn M.hermitian M.real hN
  choose S hSc hSl hSs using hFS
  let cell := qmaMediatorCell M.cell (fun e : QMALocalEvenPauliTerm M.sites => M.anchor e.val.1)
  let anchor := fun p : QMALocalEvenPauliTerm M.sites × Fin 7 => M.anchor p.1.val.1
  have hcount (p : QMAGridCell M.rows M.width) :
      (Finset.univ.filter (fun e : QMALocalEvenPauliTerm M.sites => M.anchor e.val.1 = p)).card ≤
        4^3*B := by
    have h := qmaLocalEvenPauli_filter_card M.sites M.card (fun a => M.anchor a = p)
    have hp := Nat.mul_le_mul_left (4^3) (M.termDensity p)
    simpa only using h.trans hp
  let G : QMASpatialModel 2 (A+4^3*B) (7*4^3*B) := {
    toQMARealLocalModel := {
      Q := M.Q ⊕ QMALocalEvenPauliTerm M.sites
      Term := QMALocalEvenPauliTerm M.sites × Fin 7
      qFinite := inferInstance
      qDecidable := inferInstance
      termFinite := inferInstance
      matrix := F
      sites := S
      localOn := hSl
      card := hSc
      hermitian := hFH
      real := hFR }
    rows := M.rows
    width := M.width
    cell := cell
    anchor := anchor
    geometry := by
      intro p q hq
      exact qmaMediatorSupport_geometry M.cell _ _ p.1
        (M.geometry p.1.val.1) q (hSs p hq)
    qubitDensity := by
      intro p
      change (Finset.univ.filter (fun q : M.Q ⊕ QMALocalEvenPauliTerm M.sites =>
        cell q = p)).card ≤ _
      rw [qmaSumFilter_card]
      exact Nat.add_le_add (M.qubitDensity p) (hcount p)
    termDensity := by
      intro p
      change (Finset.univ.filter (fun q : QMALocalEvenPauliTerm M.sites × Fin 7 =>
        M.anchor q.1.val.1 = p)).card ≤ _
      rw [qmaProdFilter_card (α := QMALocalEvenPauliTerm M.sites) 7 (fun e => M.anchor e.val.1 = p)]
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 7 (hcount p) }
  exact ⟨G,hFE,rfl,rfl⟩


end ContinuumCoulomb

end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMediatorGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliCongestion

namespace OAI

/-! Subdivision preserves the grid and bounded density with explicit constant factors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaProdFilter_card {α : Type*} [Fintype α] (n : ℕ) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun q : α × Fin n => p q.1)).card =
      n*(Finset.univ.filter p).card := by
  have he : (Finset.univ.filter (fun q : α × Fin n => p q.1)) =
      (Finset.univ.filter p) ×ˢ (Finset.univ : Finset (Fin n)) := by
    ext q
    simp
  rw [he,Finset.card_product]
  simp only [Finset.card_univ,Fintype.card_fin,Nat.mul_comm]

theorem QMASpatialModel.subdivision {d A B : ℕ} (M : QMASpatialModel (2*d) A B)
    {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMASpatialModel (d+1) (A+4^(2*d)*B) (4*4^(2*d)*B),
      |G.toQMARealLocalModel.energy-M.toQMARealLocalModel.energy| ≤ 1/N ∧
      G.rows = M.rows ∧ G.width = M.width := by
  obtain ⟨F,hFH,hFR,hFS,hFE⟩ := qmaLocalSubdivision_supported M.matrix M.sites M.card
    M.localOn M.hermitian M.real hN
  choose S hSc hSl hSs using hFS
  let cell := qmaMediatorCell M.cell (fun e : QMALocalEvenPauliTerm M.sites => M.anchor e.val.1)
  let anchor := fun p : QMALocalEvenPauliTerm M.sites × Fin 4 => M.anchor p.1.val.1
  have hcount (p : QMAGridCell M.rows M.width) :
      (Finset.univ.filter (fun e : QMALocalEvenPauliTerm M.sites => M.anchor e.val.1 = p)).card ≤
        4^(2*d)*B := by
    have h := qmaLocalEvenPauli_filter_card M.sites M.card (fun a => M.anchor a = p)
    have hp := Nat.mul_le_mul_left (4^(2*d)) (M.termDensity p)
    simpa only using h.trans hp
  let G : QMASpatialModel (d+1) (A+4^(2*d)*B) (4*4^(2*d)*B) := {
    toQMARealLocalModel := {
      Q := M.Q ⊕ QMALocalEvenPauliTerm M.sites
      Term := QMALocalEvenPauliTerm M.sites × Fin 4
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
      change (Finset.univ.filter (fun q : QMALocalEvenPauliTerm M.sites × Fin 4 =>
        M.anchor q.1.val.1 = p)).card ≤ _
      rw [qmaProdFilter_card (α := QMALocalEvenPauliTerm M.sites) 4 (fun e => M.anchor e.val.1 = p)]
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 4 (hcount p) }
  exact ⟨G,hFE,rfl,rfl⟩

end ContinuumCoulomb

end

end OAI

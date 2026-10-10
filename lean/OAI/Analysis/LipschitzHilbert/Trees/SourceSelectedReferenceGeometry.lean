import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedTreeData

namespace OAI

/-! Exact selected-family geometry relative to an arbitrary direction. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem selectedFamily_reference_center (Q : Finset P.PacketIndex) (t b : ℝ)
    (h : ∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤P.width/2) :
    ∀ q : (P.selectedFamily Q).PacketIndex,
      |(P.selectedFamily Q).actualZ q.1 q.2.1 q.2.2-
        t*(P.selectedFamily Q).actualX q.1 q.2.1 q.2.2-b|≤P.width/2 := by
  rintro ⟨j,l,v⟩
  exact h ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedFamily_mem Q j l v)

theorem selectedFamily_reference_slope (Q : Finset P.PacketIndex) (t Cb w : ℝ)
    (h : ∀ q∈Q, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) :
    ∀ j l, |(P.selectedFamily Q).rowSlope j l-t|≤Cb*w/(P.selectedFamily Q).length j := by
  intro j l
  obtain ⟨v,hv⟩ := P.selectedLabel_has_packet Q j l
  exact h ⟨j,⟨P.selectedOriginalLabel Q j l,v⟩⟩ hv

theorem selectedFamily_reference_energy (Q : Finset P.PacketIndex) (t cb w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    (∑ j, ∑ l : (P.selectedFamily Q).labels j, ∑ v : P.RestrictedPacketItem Q j l,
      if cb*w/(P.selectedFamily Q).length j≤|(P.selectedFamily Q).rowSlope j l-t| then
        ‖c j (P.selectedOriginalLabel Q j l) v.val‖^2*(P.selectedFamily Q).length j*P.width else 0)=
    ∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0 := by
  have h := P.sum_selectedFamily Q (fun q =>
    if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)
  simp only [Fintype.sum_sigma] at h
  exact h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

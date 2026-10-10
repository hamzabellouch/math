import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketGram
import OAI.Analysis.LipschitzHilbert.Trees.SourceInteractionGeometry

namespace OAI

/-! Removing noninteracting short packets is an exact equality for the
actual vector-valued far Gram sum. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem far_pairing_restrict_to_interacting
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S T : Finset P.PacketIndex) (gap : ℕ) :
    (∑ s∈S, ∫ z, inner ℂ (P.packetVector c s z) (P.longPacketSum c T gap s.1 z)
      ∂volume.prod volume)=
    ∑ s∈P.interactingShortPackets S T gap, ∫ z,
      inner ℂ (P.packetVector c s z) (P.longPacketSum c T gap s.1 z) ∂volume.prod volume := by
  symm
  apply Finset.sum_subset (P.interactingShortPackets_subset S T gap)
  intro s hs hout
  have hz (q : P.PacketIndex) (hq : q∈T.filter (fun q => q.1.val+gap≤s.1.val)) :
      (∫ z, inner ℂ (P.packetVector c s z) (P.packetVector c q z) ∂volume.prod volume)=0 := by
    obtain ⟨hqT,hgap⟩ := Finset.mem_filter.mp hq
    apply P.packetVector_gram_eq_zero c s q
    intro k
    by_contra hnonzero
    exact hout (Finset.mem_filter.mpr ⟨hs,q,hqT,hgap,k,hnonzero⟩)
  simp only [longPacketSum,inner_sum]
  rw [integral_finsetSum _ (fun q _ => P.packetVector_inner_integrable c s q)]
  exact Finset.sum_eq_zero (fun q hq => hz q hq)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

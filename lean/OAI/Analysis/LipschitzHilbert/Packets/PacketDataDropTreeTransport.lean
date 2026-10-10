import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDropSize
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedSum

namespace OAI

/-! Actual finite selected-tree sums after a change of starting scale. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

@[simp] theorem dropScales_treeConstant (first : Fin N) (C : ℝ) (B K : ℕ) (Lip : ℝ) :
    (P.dropScales first).referenceTreeConstant C B K Lip=P.referenceTreeConstant C B K Lip := rfl

theorem dropPackets_mono (first : Fin N) {Q R : Finset P.PacketIndex} (h : Q⊆R) :
    P.dropPackets first Q⊆P.dropPackets first R := by
  intro q hq
  exact (P.mem_dropPackets first R q).mpr (h ((P.mem_dropPackets first Q q).mp hq))

theorem dropPackets_selector_value (first : Fin N) (Q : Finset P.PacketIndex)
    (hQ : ∀ q∈Q, first.val≤q.1.val) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) :
    (∑ q∈P.dropPackets first Q, WithLp.toLp 2 (fun k =>
      c (dropIndex first q.1) q.2.1 q.2.2 k*beta (dropIndex first q.1) q.2.1 k*
      (P.dropScales first).physicalPacket t q.1 q.2.1 q.2.2 k z))=
    ∑ q∈Q, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*
      P.physicalPacket t q.1 q.2.1 q.2.2 k z) := by
  have h := P.sum_dropPackets first Q hQ (fun q => WithLp.toLp 2 (fun k =>
    c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*P.physicalPacket t q.1 q.2.1 q.2.2 k z))
  simpa only [dropPacket,P.dropScales_physicalPacket] using h

end LipschitzHilbert.PacketLatticeData

end

end OAI

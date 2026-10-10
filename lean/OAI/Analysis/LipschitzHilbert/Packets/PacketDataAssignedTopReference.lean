import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedTopFamily
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceProperties

namespace OAI

/-! The original assigned-packet cone condition gives the full-family
condition required to recenter each common-type top family. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assignedTopFamily_referenceCondition (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
    (oldSlope newSlope R cone w : ℝ)
    (hcondition : ∀ u ∈ packets, assigned u = top →
      P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    ∀ q : (P.assignedTopFamily packets assigned top).PacketIndex,
      (P.assignedTopFamily packets assigned top).referenceCondition
        oldSlope newSlope R cone w q.1 q.2.1 := by
  intro q
  have hq := (P.assignedTopPacketEquiv packets assigned top q).property
  change P.referenceCondition oldSlope newSlope R cone w q.1 q.2.1.val.2
  exact hcondition _ (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2

end LipschitzHilbert.PacketLatticeData

end

end OAI

import OAI.Analysis.LipschitzHilbert.Geometry.PacketDataSelectionRecords

namespace OAI

/-! The union of the actual recorded separated tests. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def selectedPackets (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (initial : Finset P.PacketIndex) (tops : List SlopeBox) : Finset P.PacketIndex :=
  (P.sizeSelectionRecords negative w cb A cell grid initial tops).toFinset.biUnion Prod.snd

theorem mem_selectedPackets (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (initial : Finset P.PacketIndex) (tops : List SlopeBox) (q : P.PacketIndex) :
    q∈P.selectedPackets negative w cb A cell grid initial tops ↔
      ∃ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops, q∈p.2 := by
  simp only [selectedPackets,Finset.mem_biUnion,List.mem_toFinset]

end LipschitzHilbert.PacketLatticeData

end

end OAI

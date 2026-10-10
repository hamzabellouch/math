import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLabeledGeometry
import OAI.Analysis.LipschitzHilbert.Trees.SourceInhabitedLabels

namespace OAI

/-! Removing empty labels preserves packetwise top geometry. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

 theorem inhabitedFamily_supportedTopGeometry (P : SourceLabeledLattice N κ Label Item)
    {T : SlopeBox} {K : ℝ} {D : ℕ} (G : SourceSupportedLabeledTopGeometry P T K D) :
    SourceSupportedLabeledTopGeometry P.inhabitedFamily T K D where
  length_le := fun j l u => G.length_le j (P.inhabitedOriginalLabel j l) u
  width_le := G.width_le
  centerX_le := fun j l u => G.centerX_le j (P.inhabitedOriginalLabel j l) u
  centerZ_le := fun j l u => G.centerZ_le j (P.inhabitedOriginalLabel j l) u
  order_le := G.order_le
  scale_eq := G.scale_eq

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

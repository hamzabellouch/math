import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLabeledGeometry
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorRaw
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedErrorSynthesis
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedConcentration
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledRawEnvelope

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem snapped_supported_top_horizontal {T : SlopeBox} {K : ℝ} {D : ℕ}
    (G : SourceSupportedLabeledTopGeometry P T K D) (j : Fin N) (l : P.labels j) (u : Item j l) :
    |P.length j*(P.snappedSite j l u).1-T.x| ≤ K*T.length := by
  have hs := snappedLatticeSite_horizontal (P.originX j l) (P.originZ j l)
    (P.length j) P.width (P.rowSlope j l) (P.length_pos j) (P.site j l u)
  change |P.actualX j l u-P.length j*(P.snappedSite j l u).1| ≤ P.length j at hs
  have ht := abs_sub_le (P.length j*(P.snappedSite j l u).1) (P.actualX j l u) T.x
  rw [abs_sub_comm (P.actualX j l u)] at hs
  have hg := G.centerX_le j l u
  linarith

theorem snapped_supported_top_vertical {T : SlopeBox} {K : ℝ} {D : ℕ}
    (G : SourceSupportedLabeledTopGeometry P T K D) (j : Fin N) (l : P.labels j) (u : Item j l) :
    |P.width*(P.snappedSite j l u).2-(T.y-T.slope*T.x)| ≤ K*T.width := by
  have hs := snappedLatticeSite_vertical (P.originX j l) (P.originZ j l)
    (P.length j) P.width (P.rowSlope j l) P.width_pos (P.site j l u)
  change |P.actualZ j l u-P.width*(P.snappedSite j l u).2| ≤ P.width at hs
  have ht := abs_sub_le (P.width*(P.snappedSite j l u).2) (P.actualZ j l u) (T.y-T.slope*T.x)
  rw [abs_sub_comm (P.actualZ j l u)] at hs
  have hg := G.centerZ_le j l u
  linarith

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

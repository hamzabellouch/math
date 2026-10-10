import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedPathIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedSupportedGeometry
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedInhabitedGeometry

namespace OAI

/-! Actual selected centers supply the geometry of the inhabited reference
families used by the supported plane estimate. Empty scales add no condition. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- The exact assigned-and-recentered family satisfies the supported
geometry using only the centers of packets actually assigned to this top. -/
theorem assignedInhabitedReference_supportedTopGeometry
    (P : SourceLabeledLattice N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (top : τ) (K : ℝ) (D : ℕ)
    (hwidth : P.width ≤ K*(T top).width)
    (horder : 3+2*(8*D+1) ≤ P.order)
    (hscale : P.scale = 4*(K*(T top).width))
    (hX : ∀ q ∈ packets, assigned q = top →
      |P.actualX q.1 q.2.1 q.2.2-(T top).x|+P.length q.1 ≤ K*(T top).length)
    (hZ : ∀ q ∈ packets, assigned q = top →
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T top).slope)*P.actualX q.1 q.2.1 q.2.2-
        ((T top).y-(T top).slope*(T top).x)|+P.width ≤ K*(T top).width) :
    SourceSupportedLabeledTopGeometry
      (P.assignedInhabitedReference packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency top) (T top) K D := by
  apply inhabitedFamily_supportedTopGeometry
  exact P.assignedTopReference_supportedTopGeometry packets assigned top oldSlope (R top)
    cone w F hw hcone hF hwide hfrequency (T top) K D hwidth horder hscale hX hZ

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLabeledGeometry
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedTopSelector

namespace OAI

/-! Assigned reference geometry follows from the centers of the selected
packets. No global longest-scale hypothesis is required. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)

theorem assignedTopReference_supportedTopGeometry
    (oldSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (T : SlopeBox) (K : ℝ) (D : ℕ)
    (hwidth : P.width ≤ K*T.width)
    (horder : 3+2*(8*D+1) ≤ P.order) (hscale : P.scale = 4*(K*T.width))
    (hX : ∀ q ∈ packets, assigned q = top →
      |P.actualX q.1 q.2.1 q.2.2-T.x|+P.length q.1 ≤ K*T.length)
    (hZ : ∀ q ∈ packets, assigned q = top →
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-T.slope)*P.actualX q.1 q.2.1 q.2.2-
        (T.y-T.slope*T.x)|+P.width ≤ K*T.width) :
    SourceSupportedLabeledTopGeometry
      ((P.assignedTopFamily packets assigned top).referenceFamily oldSlope T.slope R cone w F
        hw hcone hF hwide hfrequency) T K D := by
  let A := P.assignedTopFamily packets assigned top
  apply (A.referenceFamily oldSlope T.slope R cone w F
    hw hcone hF hwide hfrequency).supportedTopGeometry hwidth ?_ ?_ horder hscale
  · intro j l u
    let l' := A.referenceOriginalLabel oldSlope T.slope R cone w j l
    exact hX ⟨j,⟨l'.val.2,u.val⟩⟩
      (P.assignedTopItem_mem packets assigned top j l' u)
      (P.assignedTopItem_assignment packets assigned top j l' u)
  · intro j l u
    let l' := A.referenceOriginalLabel oldSlope T.slope R cone w j l
    have hz := A.referenceFamily_actualZ oldSlope T.slope R cone w F
      hw hcone hF hwide hfrequency j l u
    have he := congrArg (fun z : ℝ => |z-(T.y-T.slope*T.x)|+P.width) hz
    exact he.le.trans (hZ ⟨j,⟨l'.val.2,u.val⟩⟩
      (P.assignedTopItem_mem packets assigned top j l' u)
      (P.assignedTopItem_assignment packets assigned top j l' u))


end LipschitzHilbert.PacketLatticeData

end

end OAI

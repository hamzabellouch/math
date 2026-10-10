import OAI.Analysis.LipschitzHilbert.Geometry.PacketDataSignedSelectedFarBound
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedQuadratic

namespace OAI

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def selectedNearConstant (P : PacketLatticeData N κ Label Item) (gap M Q : ℕ) : ℝ :=
  ((2*gap+1:ℕ):ℝ)*(((2*Q+1)*M:ℕ):ℝ)*
    ((4*Real.pi)^2*P.profileBound^2*Real.pi^2)

def selectedFarConstant (P : PacketLatticeData N κ Label Item)
    (cb D C : ℝ) (packGap M Q : ℕ) : ℝ :=
  (4*P.profileBound*D)^2*256*
    (82944*SizeStoppingRun.selectedEnvelopePackingConstant cb packGap M Q)^2*
      1296*Real.pi^2*(((3*M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2)

end LipschitzHilbert.PacketLatticeData

end

end OAI

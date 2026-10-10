import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCrossValue
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedMaskSums

namespace OAI

/-! Literal physical top masks for unrestricted packets. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
variable (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

def physicalMaskedValue (z : ℝ×ℝ) (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2 k*
    ((T q.1 q.2.1 q.2.2).mask L A z:ℂ)*
    (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k z)

theorem physicalMaskedValue_eq_cross_at (z : ℝ×ℝ) (q : P.PacketIndex) :
    P.physicalMaskedValue alt hAlt t b v g T L A z q =
      (T q.1 q.2.1 q.2.2).mask L A z • P.crossPacketValue alt hAlt t b v g z q := by
  ext k
  simp only [physicalMaskedValue,crossPacketValue,WithLp.ofLp_toLp,PiLp.smul_apply,
    Complex.real_smul]
  ring

omit T L A in
 theorem crossPacketValue_continuous (q : P.PacketIndex) :
    Continuous (fun z => P.crossPacketValue alt hAlt t b v g z q) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  exact continuous_const.mul
    ((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).continuous

end LipschitzHilbert.PacketLatticeData

end

end OAI

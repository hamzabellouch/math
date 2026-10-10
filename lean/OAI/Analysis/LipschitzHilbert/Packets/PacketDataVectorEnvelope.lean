import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceEnvelope
import OAI.Analysis.LipschitzHilbert.Packets.PacketVectorDerivative

namespace OAI

/-! The reference-direction scalar envelope controls the actual
componentwise packet synthesis without a frequency-dimension factor. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- A coefficient vector multiplying the original physical packet. -/
def packetVector
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : P.PacketIndex) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)

theorem packetVector_reference_envelope
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (t sigma : ℝ) (q : P.PacketIndex)
    (hc : ‖c q.1 q.2.1 q.2.2‖≤sigma)
    (hclose : |(P.rowSlope q.1 q.2.1-t)*P.length q.1/P.width|≤1)
    (z : ℝ×ℝ) :
    ‖P.packetVector c q z‖≤(4*P.profileBound*sigma)*shearedTileEnvelope
      (P.actualX q.1 q.2.1 q.2.2) (P.actualZ q.1 q.2.1 q.2.2) (P.length q.1) P.width t 2 z := by
  have he : 0≤shearedTileEnvelope (P.actualX q.1 q.2.1 q.2.2)
      (P.actualZ q.1 q.2.1 q.2.2) (P.length q.1) P.width t 2 z :=
    tileEnvelope_nonneg _ _ _ _ _ _
  have hK : 0≤(4*P.profileBound)*shearedTileEnvelope
      (P.actualX q.1 q.2.1 q.2.2) (P.actualZ q.1 q.2.1 q.2.2) (P.length q.1) P.width t 2 z :=
    mul_nonneg (mul_nonneg (by norm_num) P.profileBound_pos.le) he
  have h := diagonal_packet_norm (c q.1 q.2.1 q.2.2)
    (fun k => P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) hK
    (fun k => P.physicalPacket_reference_envelope t q k hclose z)
  apply h.trans
  convert mul_le_mul_of_nonneg_left hc hK using 1
  ring

theorem packet_sum_reference_envelope
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S : Finset P.PacketIndex) (t sigma : ℝ)
    (hc : ∀ q∈S, ‖c q.1 q.2.1 q.2.2‖≤sigma)
    (hclose : ∀ q∈S, |(P.rowSlope q.1 q.2.1-t)*P.length q.1/P.width|≤1)
    (z : ℝ×ℝ) :
    ‖∑ q∈S, P.packetVector c q z‖≤(4*P.profileBound*sigma)*∑ q∈S,
      shearedTileEnvelope (P.actualX q.1 q.2.1 q.2.2) (P.actualZ q.1 q.2.1 q.2.2)
        (P.length q.1) P.width t 2 z := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun q hq => P.packetVector_reference_envelope c t sigma q
    (hc q hq) (hclose q hq) z

end LipschitzHilbert.PacketLatticeData

end

end OAI

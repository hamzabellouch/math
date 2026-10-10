import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedPrefix
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataPackedPairing

namespace OAI

/-! The distant-scale Gram contribution of an actual selected tree is
bounded by the short-packet envelope paired with its interval maximum. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem packetVector_memLp
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (q : P.PacketIndex) :
    MemLp (P.packetVector c q) 2 (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).const_mul _

def longPacketSum
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (T : Finset P.PacketIndex) (gap : ℕ) (i : Fin N) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ q∈T.filter (fun q => q.1.val+gap≤ i.val), P.packetVector c q z

theorem longPacketSum_memLp
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (T : Finset P.PacketIndex) (gap : ℕ) (i : Fin N) :
    MemLp (P.longPacketSum c T gap i) 2 (volume.prod volume) :=
  memLp_finsetSum _ (fun q _ => P.packetVector_memLp c q)

theorem far_gram_le_maximal_pairing
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S T : Finset P.PacketIndex) (gap : ℕ)
    (hI : Integrable (fun z => (∑ q∈S, ‖P.packetVector c q z‖)*
      P.physicalTreeMaximal 0 (P.onPackets T c) z) (volume.prod volume)) :
    ‖∑ q∈S, ∫ z, inner ℂ (P.packetVector c q z) (P.longPacketSum c T gap q.1 z)
      ∂volume.prod volume‖≤
        ∫ z, (∑ q∈S, ‖P.packetVector c q z‖)*
          P.physicalTreeMaximal 0 (P.onPackets T c) z ∂volume.prod volume := by
  have hi (q : P.PacketIndex) : Integrable (fun z =>
      inner ℂ (P.packetVector c q z) (P.longPacketSum c T gap q.1 z))
        (volume.prod volume) := by
    have hf := P.packetVector_memLp c q
    have hg := P.longPacketSum_memLp c T gap q.1
    exact (hf.norm.integrable_mul hg.norm).mono'
      (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => norm_inner_le_norm (𝕜 := ℂ) _ _)
  rw [←integral_finsetSum _ (fun q _ => hi q)]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (integrable_finsetSum _ (fun q _ => hi q)).norm hI
  intro z
  calc
    _ ≤ ∑ q∈S, ‖inner ℂ (P.packetVector c q z) (P.longPacketSum c T gap q.1 z)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q∈S, ‖P.packetVector c q z‖*P.physicalTreeMaximal 0 (P.onPackets T c) z := by
      apply Finset.sum_le_sum
      intro q _
      exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
        (mul_le_mul_of_nonneg_left (P.selected_long_prefix_le_maximal c T q.1 gap z)
          (norm_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

end LipschitzHilbert.PacketLatticeData

end

end OAI

import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCoefficient
import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeRestriction

namespace OAI

/-! The actual distinct-profile, masked analyzing packet sum. No auxiliary
jet is needed for the physical bilinear operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

def crossPacketValue (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (z : ℝ×ℝ) (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2 k*
    (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k z)

theorem crossPacketValue_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (q : P.PacketIndex) :
    MemLp (fun z => P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact (((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).memLp p
    (volume.prod volume)).const_mul _

theorem crossSum_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (S : Finset P.PacketIndex) :
    MemLp (fun z => ∑ q∈S, P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) :=
  memLp_finsetSum S (fun q _ => P.crossPacketValue_memLp alt hAlt t b v g p q)

end LipschitzHilbert.PacketLatticeData

end

end OAI

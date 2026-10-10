import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCrossProductForm
import OAI.Analysis.LipschitzHilbert.Packets.PacketConvolution

namespace OAI

/-! Exact passage from a physical coefficient form to the finite sum
of convolution packet products, retaining the inverse-area factor. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
open PacketRepresentation

theorem cross_kernel_form (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume))
    (KA KB : P.PacketIndex → κ → (ℝ×ℝ) → ℂ)
    (site : P.PacketIndex → ℝ×ℝ)
    (hA : ∀ q∈S, ∀ k x, P.physicalPacket 0 q.1 q.2.1 q.2.2 k x =
      synthesisWave (P.length q.1*P.width) (KA q k) (site q) x)
    (hB : ∀ q∈S, ∀ k x, (P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k x =
      analyzingWave (P.length q.1*P.width) (KB q k) (site q) x) :
    (∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q) (f z)
      ∂volume.prod volume) =
      ∑ q∈S, ∑ k, ((P.length q.1*P.width:ℝ):ℂ)⁻¹*
        packetProduct (KA q k) (KB q k) (fun z => f z k)
          (fun z => b q.1 q.2.1 k (u z)) (fun z => g z k)
          (P.length q.1*P.width) (site q) := by
  rw [P.cross_product_form alt hAlt S b u g f hf]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [hA q hq k, hB q hq k]
  rw [packetProduct,coefficient]
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI

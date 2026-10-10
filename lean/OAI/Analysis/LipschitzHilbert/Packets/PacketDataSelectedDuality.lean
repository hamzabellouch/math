import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedDuality
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedGram

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

namespace PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- Coefficients of the original physical packets, before selector masks. -/
def ordinaryCoefficient (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun q : P.PacketIndex => P.length q.1*P.width)
    (fun q k => P.physicalPacket 0 q.1 q.2.1 q.2.2 k) g ⟨j,⟨l,u⟩⟩

 theorem selected_ordinary_coefficient_energy (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hg : MemLp g 2 (volume.prod volume)) (S : Finset P.PacketIndex)
    (A : ℝ) (hA : 0≤A)
    (hbound : (∫ z, ‖∑ q∈S, P.packetVector (P.ordinaryCoefficient g) q z‖^2
      ∂volume.prod volume)≤A*P.packetEnergySum (P.ordinaryCoefficient g) S) :
    P.packetEnergySum (P.ordinaryCoefficient g) S≤A*∫ z, ‖g z‖^2 ∂volume.prod volume := by
  have he : P.packetEnergySum (P.ordinaryCoefficient g) S=
      ∑ q∈S, (P.length q.1*P.width)*‖P.ordinaryCoefficient g q.1 q.2.1 q.2.2‖^2 := by
    apply Finset.sum_congr rfl
    intro q _
    ring
  apply l2_self_pairing_energy_le (volume.prod volume) _ g _ A _ hA
    (memLp_finsetSum S (fun q _ => P.packetVector_memLp (P.ordinaryCoefficient g) q)) hg _ hbound
  · exact Finset.sum_nonneg fun q _ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  · rw [he]
    apply finite_analyzing_self_pairing
    · intro q _
      exact (mul_pos (P.length_pos q.1) P.width_pos).ne'
    · intro q _ k
      have hgk : MemLp (fun z => g z k) 2 (volume.prod volume) := (memLp_piLp_iff.mp hg) k
      exact hgk.integrable_mul ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2
        (volume.prod volume)).star

end PacketLatticeData
end LipschitzHilbert

end

end OAI

import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingBilinear
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelEstimate
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCoefficient
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedDuality

namespace OAI

/-! Literal finite adjoint duality for the ordinary masked packets. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def ordinaryForwardSum (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ q∈S, WithLp.toLp 2 (fun k => P.ordinaryCoefficient f q.1 q.2.1 q.2.2 k*
    b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)

def ordinaryAdjointSum (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ q∈S, P.packetVector (P.physicalMultiplierCoefficient 0 b u g) q z

theorem masked_physical_packet_memLp
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (q : P.PacketIndex) (k : κ) :
    MemLp (fun z => b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      2 (volume.prod volume) := by
  apply ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).mono
    ((((hb q.1 q.2.1 k).comp hu).mul
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k).continuous.measurable).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z‖≤_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb1 q.1 q.2.1 k (u z))

theorem ordinaryAdjointSum_memLp (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    MemLp (P.ordinaryAdjointSum S b u g) 2 (volume.prod volume) :=
  memLp_finsetSum S (fun q _ => P.packetVector_memLp _ q)

theorem ordinary_forward_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : MemLp g 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryForwardSum S b u f z) (g z) ∂volume.prod volume)=
      ∑ q∈S, ((P.length q.1*P.width:ℝ):ℂ)*inner ℂ
        (P.ordinaryCoefficient f q.1 q.2.1 q.2.2)
        (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2) := by
  let area := fun q : P.PacketIndex => P.length q.1*P.width
  let masked := fun (q : P.PacketIndex) (k : κ) (z : ℝ×ℝ) =>
    b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z
  let cf := fun q : P.PacketIndex => P.ordinaryCoefficient f q.1 q.2.1 q.2.2
  have ha (q : P.PacketIndex) (_hq : q∈S) : area q≠0 := (mul_pos (P.length_pos _) P.width_pos).ne'
  have hm (q : P.PacketIndex) (_hq : q∈S) (k : κ) :
      Integrable (fun z => g z k*conj (masked q k z)) (volume.prod volume) :=
    ((memLp_piLp_iff.mp hg) k).integrable_mul (P.masked_physical_packet_memLp b hb hb1 u hu q k).star
  have h := finite_analyzing_pairing (volume.prod volume) area masked g cf S ha hm
  have he (z : ℝ×ℝ) : (∑ q∈S, WithLp.toLp 2 (fun k => cf q k*masked q k z))=
      P.ordinaryForwardSum S b u f z := by
    apply Finset.sum_congr rfl
    intro q _
    apply WithLp.ofLp_injective
    funext k
    change cf q k*(b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)=
      cf q k*b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z
    ring
  have hc (q : P.PacketIndex) : analyzingCoefficient (volume.prod volume) area masked g q=
      P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 := rfl
  simp_rw [he,hc] at h
  exact h

theorem ordinary_adjoint_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : MemLp f 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume)=
      ∑ q∈S, ((P.length q.1*P.width:ℝ):ℂ)*inner ℂ
        (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2)
        (P.ordinaryCoefficient f q.1 q.2.1 q.2.2) := by
  apply finite_analyzing_pairing (volume.prod volume)
    (fun q : P.PacketIndex => P.length q.1*P.width)
    (fun q k => P.physicalPacket 0 q.1 q.2.1 q.2.2 k) f
    (fun q => P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2) S
  · intro q _
    exact (mul_pos (P.length_pos _) P.width_pos).ne'
  · intro q _ k
    exact ((memLp_piLp_iff.mp hf) k).integrable_mul
      ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).star

theorem ordinary_forward_adjoint_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryForwardSum S b u f z) (g z) ∂volume.prod volume)=
      conj (∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume) := by
  rw [P.ordinary_forward_pairing S b hb hb1 u hu f g hg,P.ordinary_adjoint_pairing S b u f g hf,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_mul,Complex.conj_ofReal,inner_conj_symm]

end LipschitzHilbert.PacketLatticeData

end

end OAI

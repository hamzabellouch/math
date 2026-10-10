import OAI.Analysis.LipschitzHilbert.Packets.PacketDataPolarization
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAdjoint
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCrossValue
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledCrossIdentity

namespace OAI

/-! Exact polarization for masked analyzing coefficients and their
unmasked, distinct-profile adjoint synthesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

theorem polarize_multiplier_coefficient (c : ℂ) (hc : ‖c‖=1)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (j : Fin N) (l : P.labels j) (a : Item j l) :
    (P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g j l a=
      P.physicalMultiplierCoefficient 0 b u g j l a+
        conj c • (P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g j l a := by
  let f := fun (a : Item j l) (k : κ) (z : ℝ×ℝ) => b j l k (u z)*P.physicalPacket 0 j l a k z
  let h := fun (a : Item j l) (k : κ) (z : ℝ×ℝ) =>
    b j l k (u z)*(P.withProfile alt hAlt).physicalPacket 0 j l a k z
  have he : (fun (a : Item j l) (k : κ) (z : ℝ×ℝ) =>
      b j l k (u z)*(P.polarize alt hAlt c hc).physicalPacket 0 j l a k z)=
      fun a k z => f a k z+c*h a k z := by
    funext a k z
    rw [P.polarize_physicalPacket alt hAlt c hc]
    change b j l k (u z)*(P.physicalPacket 0 j l a k z+c*(P.withProfile alt hAlt).physicalPacket 0 j l a k z)=_
    dsimp only [f,h]
    ring
  change analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (fun a k z => b j l k (u z)*(P.polarize alt hAlt c hc).physicalPacket 0 j l a k z) g a=_
  rw [he]
  exact analyzingCoefficient_add_smul (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    f h g c
    (fun a k => P.physical_multiplier_analyzing_integrable 0 (fun z => b j l k (u z))
      ((hb j l k).comp hu) (fun z => hb1 j l k (u z)) g hg hg1 j l a k)
    (fun a k => (P.withProfile alt hAlt).physical_multiplier_analyzing_integrable 0 (fun z => b j l k (u z))
      ((hb j l k).comp hu) (fun z => hb1 j l k (u z)) g hg hg1 j l a k) a

theorem cross_adjoint_polarization (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (z : ℝ×ℝ) :
    (4:ℂ) • (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)=
      (P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum S b u g z-
      (P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum S b u g z-
      Complex.I • (P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum S b u g z+
      Complex.I • (P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum S b u g z := by
  have hcross (q : P.PacketIndex) : P.crossPacketValue alt hAlt 0 b u g z q=
      WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k*
        (P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z) := rfl
  have hterm (c : ℂ) (hc : ‖c‖=1) (q : P.PacketIndex) (k : κ) :
      (P.polarize alt hAlt c hc).packetVector
        ((P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g) q z k=
      (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k+
        conj c*(P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)*
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z+c*(P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z) := by
    change (P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k*
      (P.polarize alt hAlt c hc).physicalPacket 0 q.1 q.2.1 q.2.2 k z=_
    rw [P.polarize_multiplier_coefficient alt hAlt c hc b hb hb1 u hu g hg hg1,
      P.polarize_physicalPacket alt hAlt c hc]
    simp only [PiLp.add_apply,PiLp.smul_apply,add_apply,smul_apply,smul_eq_mul]
  apply WithLp.ofLp_injective
  funext k
  simp only [hcross,ordinaryAdjointSum,WithLp.ofLp_sum,Finset.sum_apply,
    WithLp.ofLp_smul,WithLp.ofLp_add,WithLp.ofLp_sub,
    Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  simp only [hterm]
  simp only [map_one,map_neg,Complex.conj_I,one_mul,neg_mul,neg_neg,
    Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have h := packet_cross_polarization
    (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)
    ((P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)
    (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
    ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  linear_combination -h

end LipschitzHilbert.PacketLatticeData

end

end OAI

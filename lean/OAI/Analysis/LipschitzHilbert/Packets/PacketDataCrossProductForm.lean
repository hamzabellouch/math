import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCrossForm

namespace OAI

/-! Expansion into the two literal wave integrals. This is the finite
form to which the translated convolution packet identity applies. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem cross_product_form (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) :
    (∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q) (f z)
      ∂volume.prod volume) =
      ∑ q∈S, ∑ k, ((P.length q.1*P.width:ℝ):ℂ)⁻¹*
        (∫ z, f z k*conj ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z)
          ∂volume.prod volume)*
        (∫ z, b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z*conj (g z k)
          ∂volume.prod volume) := by
  rw [P.cross_coefficient_form alt hAlt S b u g f hf]
  apply Finset.sum_congr rfl
  intro q _
  simp only [PiLp.inner_apply,RCLike.inner_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hc : conj (∫ z, g z k*conj (b q.1 q.2.1 k (u z)*
      P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) ∂volume.prod volume) =
      ∫ z, b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z*conj (g z k)
        ∂volume.prod volume := by
    rw [←integral_conj]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [map_mul,starRingEnd_self_apply]
    ring
  simp only [ordinaryCoefficient,physicalMultiplierCoefficient,analyzingCoefficient,
    WithLp.ofLp_toLp]
  have hlen : (P.withProfile alt hAlt).length q.1 = P.length q.1 := rfl
  have hwidth : (P.withProfile alt hAlt).width = P.width := rfl
  simp only [hlen,hwidth]
  rw [map_mul,map_inv₀,Complex.conj_ofReal,hc]
  have ha : (↑(P.length q.1*P.width):ℂ)≠0 := by
    exact_mod_cast (mul_pos (P.length_pos q.1) P.width_pos).ne'
  field_simp

end LipschitzHilbert.PacketLatticeData

end

end OAI

import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensity
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabelScaleEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedLattice
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeScaleEnergy

namespace OAI

/-! The actual source family has a fixed-scale synthesis bound using
only local angular multiplicity, uniformly in its total label count. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem physicalPacket_label_envelope (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (z : ℝ×ℝ) :
    ‖P.physicalPacket 0 j l u k z‖≤P.profileBound*
      (lineEnvelope (P.originX j l+P.length j*(P.site j l u).1) (P.length j) 1 z.1*
        lineEnvelope (P.originZ j l-P.rowSlope j l*P.originX j l+P.width*(P.site j l u).2)
          P.width 1 (z.2-P.rowSlope j l*z.1)) := by
  have h := physicalPlanarPacket_profile_envelope (P.profile j l u k) (2*P.order)
    (P.actualX j l u) (P.actualZ j l u) (P.length j) P.width
    (P.rowSlope j l) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne' z
  have horder : 1≤2*P.order := by have := P.order_ge_three; omega
  have hcenter : P.actualZ j l u-P.rowSlope j l*P.actualX j l u=
      P.originZ j l-P.rowSlope j l*P.originX j l+P.width*(P.site j l u).2 := by
    simp only [actualX,actualZ]
    ring
  rw [hcenter] at h
  apply (show ‖P.physicalPacket 0 j l u k z‖≤_ from by
    simpa only [physicalPacket,zero_mul,add_zero,zero_add] using h).trans
  exact mul_le_mul (P.profile_bound j l u k)
    (mul_le_mul (lineEnvelope_antitone _ _ _ horder) (lineEnvelope_antitone _ _ _ horder)
      (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    P.profileBound_pos.le

theorem physicalPacket_local_label_scale_energy (j : Fin N)
    (c : ∀ l : P.labels j, Item j l → EuclideanSpace ℂ κ)
    (w cStar cEta CEta : ℝ) (hw : 0<w) (hcEta : 0<cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hspectrum : ∀ l u k xi eta,
      planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    (∫ z, ‖∑ l : P.labels j, planarFixedSynthesis (c l) (P.physicalPacket 0 j l) z‖^2
      ∂volume.prod volume)≤
      (((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
        ∑ l : P.labels j, ∑ u, ‖c l u‖^2*P.length j*P.width := by
  exact planar_label_scale_energy c (P.physicalPacket 0 j) (P.site j) (P.site_injective j)
    (P.originX j) (fun l => P.originZ j l-P.rowSlope j l*P.originX j l)
    (P.rowSlope j) (P.length j) P.width P.profileBound w cStar cEta CEta
    (P.length_pos j) P.width_pos hw hcEta M Q hQ hmultiplicity hspectrum
    (P.physicalPacket_label_envelope j)

end LipschitzHilbert.PacketLatticeData

end

end OAI

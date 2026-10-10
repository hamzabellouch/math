import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedGram
import OAI.Analysis.LipschitzHilbert.Geometry.SourceFarLinear

namespace OAI

/-! Linear summation of the per-top quadratic estimate, using the
actual stopping threshold for each recorded top. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item}
  {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

namespace SizeStoppingRun

theorem selected_far_linear
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (gap : ℕ) (K : ℝ) (hK : 0≤K)
    (hquad : ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      ‖P.farPairing c (P.selectedPackets negative w cb A cell grid initial tops) p.2 gap‖^2≤
        K*sigma^2*p.1.length*P.width*P.packetEnergySum c p.2) :
    ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      ‖P.farPairing c (P.selectedPackets negative w cb A cell grid initial tops) p.2 gap‖≤
        Real.sqrt (2*K)*P.packetEnergySum c p.2 := by
  intro p hp
  have he : 0≤P.packetEnergySum c p.2 :=
    Finset.sum_nonneg fun q _ => mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  have hwidth := (h.records_geometry p hp).1
  apply quadratic_far_bound_linear he hK (sigma := sigma) (A := p.1.area)
  · have hq := hquad p hp
    simpa only [SlopeBox.area,hwidth,mul_assoc] using hq
  · exact h.recorded_energy_lower p hp

theorem selected_gram_energy_of_quadratic
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hA : 1/2≤A) (gap : ℕ) (Cnear K : ℝ) (hK : 0≤K)
    (hnear : let S := P.selectedPackets negative w cb A cell grid initial tops
      (∑ s∈S, ∑ q∈S, if |(s.1.val:ℤ)-(q.1.val:ℤ)|≤(gap:ℤ) then
        (inner ℂ (P.packetL2 c s) (P.packetL2 c q)).re else 0)≤Cnear*P.packetEnergySum c S)
    (hquad : ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      ‖P.farPairing c (P.selectedPackets negative w cb A cell grid initial tops) p.2 (gap+1)‖^2≤
        K*sigma^2*p.1.length*P.width*P.packetEnergySum c p.2) :
    let S := P.selectedPackets negative w cb A cell grid initial tops
    (∫ z, ‖∑ q∈S, P.packetVector c q z‖^2 ∂volume.prod volume)≤
      (Cnear+2*Real.sqrt (2*K))*P.packetEnergySum c S :=
  P.selected_gram_energy negative w cb A hA cell grid c initial tops gap Cnear
    (Real.sqrt (2*K)) hnear (h.selected_far_linear (gap+1) K hK hquad)

end SizeStoppingRun
end LipschitzHilbert.PacketLatticeData

end

end OAI

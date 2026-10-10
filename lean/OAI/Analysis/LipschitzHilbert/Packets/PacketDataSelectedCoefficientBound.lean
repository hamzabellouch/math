import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedPackets
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSizeOnePacket

namespace OAI

/-! The initial unsigned size bound controls each coefficient recorded
by either signed pass. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ} {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_coefficient_bound
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hcb : cb≤1/4) (D : ℝ) (hD : 0≤D) (hsigma : 0≤sigma)
    (hsize : ∀ T : SlopeBox, T.width=P.width → T.length≤tau →
      P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) :
    ∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
      ‖c q.1 q.2.1 q.2.2‖≤D*sigma := by
  intro q hq
  obtain ⟨p,hp,hqp⟩ := (P.mem_selectedPackets negative w cb A cell grid initial tops q).mp hq
  have hgeom := h.records_geometry p hp
  exact P.coefficient_le_of_size_tests w cb tau (D*sigma) hw hcb (mul_nonneg hD hsigma)
    cell grid c initial hsize q
    (P.sizeSelectionRecords_subset negative w cb A cell grid initial tops p hp hqp)
    (((hgeom.2.2 q hqp).1).trans hgeom.2.1)

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI

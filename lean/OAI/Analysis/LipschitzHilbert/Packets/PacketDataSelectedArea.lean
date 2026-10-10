import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedDuality

namespace OAI

/-! Charge the actual selected top areas to the L2 norm of the test
function, using the proved selected synthesis estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ} {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_top_area_bound
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : MemLp g 2 (volume.prod volume))
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid
      (P.ordinaryCoefficient g) initial tops remaining)
    (hA : 1/2≤A) (hsigma : 0<sigma) (C : ℝ) (hC : 0≤C)
    (hbound : let S := P.selectedPackets negative w cb A cell grid initial tops
      (∫ z, ‖∑ q∈S, P.packetVector (P.ordinaryCoefficient g) q z‖^2 ∂volume.prod volume)≤
        C*P.packetEnergySum (P.ordinaryCoefficient g) S) :
    (tops.map SlopeBox.area).sum≤(2*C/sigma^2)*∫ z, ‖g z‖^2 ∂volume.prod volume := by
  have he := P.selected_ordinary_coefficient_energy g hg
    (P.selectedPackets negative w cb A cell grid initial tops) C hC hbound
  have ht := h.top_area_energy
  rw [←h.selected_energy_eq_records hA] at ht
  have hle : sigma^2/2*(tops.map SlopeBox.area).sum≤C*∫ z, ‖g z‖^2 ∂volume.prod volume :=
    ht.trans he
  have hs : 0<sigma^2/2 := div_pos (sq_pos_of_pos hsigma) (by norm_num)
  calc
    _ ≤ (C*∫ z, ‖g z‖^2 ∂volume.prod volume)/(sigma^2/2) :=
      (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hle)
    _ = _ := by field_simp

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI

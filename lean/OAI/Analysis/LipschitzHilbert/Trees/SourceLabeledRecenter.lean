import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketShear
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledRawEnvelope

namespace OAI

/-! Recenter a selected labelled lattice on its tree direction. Sites
and profiles remain original, and the shear preserves physical packets. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def recenter (t M : ℝ) (hM : 0≤M)
    (hshear : ∀ j l, |(P.rowSlope j l-t)*P.length j/P.width|≤1)
    (hcarrier : ∀ j l k, |P.frequency k*(P.rowSlope j l-t)*P.length j|≤M) :
    SourceLabeledLattice N κ Label Item :=
  { P with
    carrierBound := M
    carrierBound_nonneg := hM
    originZ := fun j l => P.originZ j l-t*P.originX j l
    rowSlope := fun j l => P.rowSlope j l-t
    shear_bound := hshear
    carrier_bound := hcarrier }

theorem recenter_cone_bounds (t H F w : ℝ) (hw : 0<w) (hF : 0≤F)
    (hwide : H*w≤P.width)
    (hcone : ∀ j l, |P.rowSlope j l-t|≤H*w/P.length j)
    (hfrequency : ∀ k, |P.frequency k|≤F/w) :
    (∀ j l, |(P.rowSlope j l-t)*P.length j/P.width|≤1) ∧
      ∀ j l k, |P.frequency k*(P.rowSlope j l-t)*P.length j|≤F*H := by
  have hr (j : Fin N) (l : P.labels j) : |P.rowSlope j l-t| *P.length j≤H*w :=
    (le_div_iff₀ (P.length_pos j)).mp (hcone j l)
  constructor
  · intro j l
    rw [abs_div,abs_mul,abs_of_pos (P.length_pos j),abs_of_pos P.width_pos]
    exact (div_le_one P.width_pos).mpr ((hr j l).trans hwide)
  · intro j l k
    rw [abs_mul,abs_mul,abs_of_pos (P.length_pos j),mul_assoc]
    calc
      _ ≤ (F/w)*(H*w) := mul_le_mul (hfrequency k) (hr j l)
        (mul_nonneg (abs_nonneg _) (P.length_pos j).le) (div_nonneg hF hw.le)
      _ = F*H := by field_simp


variable (t M : ℝ) (hM : 0≤M)
  (hshear : ∀ j l, |(P.rowSlope j l-t)*P.length j/P.width|≤1)
  (hcarrier : ∀ j l k, |P.frequency k*(P.rowSlope j l-t)*P.length j|≤M)

@[simp] theorem recenter_length (j : Fin N) :
    (P.recenter t M hM hshear hcarrier).length j=P.length j := rfl

@[simp] theorem recenter_absoluteConstant :
    (P.recenter t M hM hshear hcarrier).absoluteConstant=P.absoluteConstant := rfl

@[simp] theorem recenter_actualX (j : Fin N) (l : P.labels j) (u : Item j l) :
    (P.recenter t M hM hshear hcarrier).actualX j l u=P.actualX j l u := rfl

theorem recenter_actualZ (j : Fin N) (l : P.labels j) (u : Item j l) :
    (P.recenter t M hM hshear hcarrier).actualZ j l u=P.actualZ j l u-t*P.actualX j l u := by
  dsimp [actualZ,actualX,recenter,length]
  ring

theorem recenter_physicalPacket (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) (z : ℝ×ℝ) :
    (P.recenter t M hM hshear hcarrier).physicalPacket 0 j l u k z=
      P.physicalPacket 0 j l u k (LipschitzHilbert.slopeShear t z) := by
  simp only [physicalPacket,physicalPlanarPacket_apply,zero_mul,add_zero,zero_add]
  rw [P.recenter_actualX,P.recenter_actualZ]
  change Complex.exp (((P.frequency k*
    ((z.2-(P.actualZ j l u-t*P.actualX j l u))-
      (P.rowSlope j l-t)*(z.1-P.actualX j l u))):ℝ)*Complex.I)*
    P.profile j l u k ((z.1-P.actualX j l u)/P.length j,
      ((z.2-(P.actualZ j l u-t*P.actualX j l u))-
        (P.rowSlope j l-t)*(z.1-P.actualX j l u))/P.width)=_
  have he : (z.2-(P.actualZ j l u-t*P.actualX j l u))-
      (P.rowSlope j l-t)*(z.1-P.actualX j l u)=
      ((z.2+t*z.1)-P.actualZ j l u)-P.rowSlope j l*(z.1-P.actualX j l u) := by ring
  rw [he]
  rfl

theorem recenter_fourier (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) (xi eta : ℝ) :
    LipschitzHilbert.planarAngularFourier
      ((P.recenter t M hM hshear hcarrier).physicalPacket 0 j l u k) (xi,eta)=
      LipschitzHilbert.planarAngularFourier (P.physicalPacket 0 j l u k) (xi-t*eta,eta) := by
  have he : ((P.recenter t M hM hshear hcarrier).physicalPacket 0 j l u k : ℝ×ℝ → ℂ)=
      fun z => P.physicalPacket 0 j l u k (LipschitzHilbert.slopeShear t z) := by
    funext z
    exact P.recenter_physicalPacket t M hM hshear hcarrier j l u k z
  rw [he,LipschitzHilbert.planarAngularFourier_slopeShear]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

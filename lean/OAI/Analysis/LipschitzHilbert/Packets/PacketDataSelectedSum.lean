import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedGeometry

namespace OAI

/-! Exact synthesis and separated-energy identities for the selected
reference lattice, with its cost expressed only in the original fixed
profile bounds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def referenceEnvelopeConstant : ℝ :=
  ((2^P.order*P.profileBound)*P.ratioBound^2)*3^(2*P.order)

theorem referenceEnvelopeConstant_pos :
    0<P.referenceEnvelopeConstant := by
  have hp := P.profileBound_pos
  have hr : 0<P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  unfold referenceEnvelopeConstant
  positivity

def referenceTreeConstant (C : ℝ) (B K : ℕ) (Lip : ℝ) : ℝ :=
  27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*P.profileBound+
  Real.sqrt (C*(B:ℝ))*P.referenceEnvelopeConstant+
  32^106*(B:ℝ)*P.referenceEnvelopeConstant*(2+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4)*
    (32*2^203)*9*transverseTailConstant

variable (S : Finset P.PacketIndex) (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)
local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

def selectedCoefficients (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    ∀ j (l : (Q).labels j), P.SelectedItem S j l → EuclideanSpace ℂ κ :=
  fun j l u => c j (P.selectedOriginalLabel S j l) u.val

def selectedMultipliers (beta : ∀ j, P.labels j → κ → ℂ) :
    ∀ j, (Q).labels j → κ → ℂ := fun j l => beta j (P.selectedOriginalLabel S j l)

theorem selectedReference_constant (C : ℝ) (B K : ℕ) (Lip : ℝ) :
    (Q).ordinaryTreeConstant C B K Lip=P.referenceTreeConstant C B K Lip := rfl

theorem selectedReference_synthesis
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) :
    (Q).physicalTreeSelectorValue t
      (P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c)
      (P.selectedMultipliers S t Cb w F hw hCb hF hwide hfrequency hnear beta) z =
    ∑ q∈S, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*
      P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) := by
  let value := fun q : P.PacketIndex => WithLp.toLp 2
    (fun k => c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  have hval (r : (Q).PacketIndex) :
      WithLp.toLp 2 (fun k =>
        P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c r.1 r.2.1 r.2.2 k*
        P.selectedMultipliers S t Cb w F hw hCb hF hwide hfrequency hnear beta r.1 r.2.1 k*
        (Q).physicalPacket t r.1 r.2.1 r.2.2 k z) =
      value (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear r).val := by
    rcases r with ⟨j,l,u⟩
    apply WithLp.ofLp_injective
    funext k
    simp only [selectedCoefficients,selectedMultipliers,value,selectedReferenceEquiv]
    rw [P.selectedReference_physicalPacket S t Cb w F hw hCb hF hwide hfrequency hnear j l u k]
    rfl
  calc
    _ = ∑ r : (Q).PacketIndex, WithLp.toLp 2 (fun k =>
        P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c r.1 r.2.1 r.2.2 k*
        P.selectedMultipliers S t Cb w F hw hCb hF hwide hfrequency hnear beta r.1 r.2.1 k*
        (Q).physicalPacket t r.1 r.2.1 r.2.2 k z) := by
      simp only [SourceLabeledLattice.physicalTreeSelectorValue,Fintype.sum_sigma]
    _ = ∑ r : (Q).PacketIndex,
        value (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear r).val :=
      Finset.sum_congr rfl (fun r _ => hval r)
    _ = _ := P.selectedReference_sum S t Cb w F hw hCb hF hwide hfrequency hnear value

theorem selectedReference_separated_energy
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (cb : ℝ) :
    (Q).angularSeparatedTreeEnergy cb w
      (P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c) =
    ∑ q∈S, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0 := by
  have h := P.selectedReference_sum S t Cb w F hw hCb hF hwide hfrequency hnear
    (fun q => if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)
  simp only [Fintype.sum_sigma] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI

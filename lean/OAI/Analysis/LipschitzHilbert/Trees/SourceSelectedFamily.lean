import OAI.Analysis.LipschitzHilbert.Packets.SourceLabeledPacketRestriction
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlopeLabels
import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularOrdinaryTree

namespace OAI

/-! A selected packet set as its exact finite lattice family. Empty
labels are removed, so row bounds follow from actual selected packets. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def selectedLabels (Q : Finset P.PacketIndex) (j : Fin N) : Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ (h : l∈P.labels j) (u : Item j l),
    (⟨j,⟨⟨l,h⟩,u⟩⟩ : P.PacketIndex)∈Q)

def selectedOriginalLabel (Q : Finset P.PacketIndex) (j : Fin N)
    (l : P.selectedLabels Q j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

def selectedFamily (Q : Finset P.PacketIndex) :
    SourceLabeledLattice N κ Label (P.RestrictedPacketItem Q) where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := P.carrierBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := P.carrierBound_nonneg
  labels := P.selectedLabels Q
  originX := fun j l => P.originX j (P.selectedOriginalLabel Q j l)
  originZ := fun j l => P.originZ j (P.selectedOriginalLabel Q j l)
  rowSlope := fun j l => P.rowSlope j (P.selectedOriginalLabel Q j l)
  frequency := P.frequency
  site := fun j l u => P.site j (P.selectedOriginalLabel Q j l) u.val
  site_injective := fun j l => (P.site_injective j (P.selectedOriginalLabel Q j l)).comp
    Subtype.val_injective
  profile := fun j l u k => P.profile j (P.selectedOriginalLabel Q j l) u.val k
  profile_bound := fun j l u k => P.profile_bound j (P.selectedOriginalLabel Q j l) u.val k
  shear_bound := fun j l => P.shear_bound j (P.selectedOriginalLabel Q j l)
  carrier_bound := fun j l k => P.carrier_bound j (P.selectedOriginalLabel Q j l) k

def selectedPacketEquiv (Q : Finset P.PacketIndex) : (P.selectedFamily Q).PacketIndex ≃ Q where
  toFun := fun q => ⟨⟨q.1,⟨P.selectedOriginalLabel Q q.1 q.2.1,q.2.2.val⟩⟩,by
    obtain ⟨h,hm⟩ := q.2.2.property
    exact hm⟩
  invFun := fun q => ⟨q.val.1,⟨
    ⟨q.val.2.1.val,Finset.mem_filter.mpr ⟨q.val.2.1.property,
      ⟨q.val.2.1.property,q.val.2.2,q.property⟩⟩⟩,
    ⟨q.val.2.2,⟨q.val.2.1.property,q.property⟩⟩⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem selectedFamily_mem (Q : Finset P.PacketIndex) (j : Fin N)
    (l : (P.selectedFamily Q).labels j) (v : P.RestrictedPacketItem Q j l) :
    (⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ : P.PacketIndex)∈Q := by
  obtain ⟨h,hm⟩ := v.property
  exact hm

theorem selectedLabel_has_packet (Q : Finset P.PacketIndex) (j : Fin N)
    (l : (P.selectedFamily Q).labels j) :
    ∃ u : Item j l, (⟨j,⟨P.selectedOriginalLabel Q j l,u⟩⟩ : P.PacketIndex)∈Q := by
  obtain ⟨h,u,hu⟩ := (Finset.mem_filter.mp l.property).2
  exact ⟨u,hu⟩

@[simp] theorem selectedFamily_length (Q : Finset P.PacketIndex) (j : Fin N) :
    (P.selectedFamily Q).length j=P.length j := rfl

@[simp] theorem selectedFamily_physicalPacket (Q : Finset P.PacketIndex) (t : ℝ)
    (j : Fin N) (l : (P.selectedFamily Q).labels j)
    (u : P.RestrictedPacketItem Q j l) (k : κ) :
    (P.selectedFamily Q).physicalPacket t j l u k=
      P.physicalPacket t j (P.selectedOriginalLabel Q j l) u.val k := rfl

@[simp] theorem selectedFamily_absoluteConstant (Q : Finset P.PacketIndex) :
    (P.selectedFamily Q).absoluteConstant=P.absoluteConstant := rfl

theorem sum_selectedFamily {E : Type*} [AddCommMonoid E] (Q : Finset P.PacketIndex)
    (f : P.PacketIndex → E) :
    (∑ q : (P.selectedFamily Q).PacketIndex, f (P.selectedPacketEquiv Q q).val)=
      ∑ q∈Q, f q := by
  have h := Equiv.sum_comp (P.selectedPacketEquiv Q) (fun q : Q => f q.val)
  exact h.trans (Finset.sum_subtype Q (p := fun q => q∈Q) (by simp) f).symm

theorem selectedFamily_energy (Q : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    (∑ j, ∑ l : (P.selectedFamily Q).labels j, ∑ u : P.RestrictedPacketItem Q j l,
      ‖c j (P.selectedOriginalLabel Q j l) u.val‖^2*(P.selectedFamily Q).length j*
        (P.selectedFamily Q).width)=
      ∑ q∈Q, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
  have h := P.sum_selectedFamily Q
    (fun q => ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width)
  simp only [Fintype.sum_sigma] at h
  exact h

@[simp] theorem selectedFamily_actualX (Q : Finset P.PacketIndex) (j : Fin N)
    (l : (P.selectedFamily Q).labels j) (u : P.RestrictedPacketItem Q j l) :
    (P.selectedFamily Q).actualX j l u=P.actualX j (P.selectedOriginalLabel Q j l) u.val := rfl

@[simp] theorem selectedFamily_actualZ (Q : Finset P.PacketIndex) (j : Fin N)
    (l : (P.selectedFamily Q).labels j) (u : P.RestrictedPacketItem Q j l) :
    (P.selectedFamily Q).actualZ j l u=P.actualZ j (P.selectedOriginalLabel Q j l) u.val := rfl

theorem selectedFamily_selector_value (Q : Finset P.PacketIndex) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) :
    (P.selectedFamily Q).physicalTreeSelectorValue t
      (fun j l u => c j (P.selectedOriginalLabel Q j l) u.val)
      (fun j l k => beta j (P.selectedOriginalLabel Q j l) k) z=
      ∑ q∈Q, WithLp.toLp 2 (fun k =>
        c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*P.physicalPacket t q.1 q.2.1 q.2.2 k z) := by
  unfold physicalTreeSelectorValue
  have h := P.sum_selectedFamily Q (fun q => WithLp.toLp 2 (fun k =>
    c q.1 q.2.1 q.2.2 k*beta q.1 q.2.1 k*P.physicalPacket t q.1 q.2.1 q.2.2 k z))
  simp only [Fintype.sum_sigma] at h
  exact h

theorem selectedFamily_separated_energy (Q : Finset P.PacketIndex) (cb w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    (P.selectedFamily Q).angularSeparatedTreeEnergy cb w
      (fun j l u => c j (P.selectedOriginalLabel Q j l) u.val)=
      ∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1| then
        ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0 := by
  unfold angularSeparatedTreeEnergy
  have h := P.sum_selectedFamily Q (fun q =>
    if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)
  simp only [Fintype.sum_sigma] at h
  exact h

@[simp] theorem selectedFamily_ordinaryDensity (Q : Finset P.PacketIndex) (t w tau : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (E : Set (ℝ×ℝ)) (v : ℝ×ℝ → ℝ) (q : (P.selectedFamily Q).PacketIndex) :
    (P.selectedFamily Q).ordinaryDensity t
      (fun j l => cell j (P.selectedOriginalLabel Q j l)) grid w tau E v q=
      P.ordinaryDensity t cell grid w tau E v (P.selectedPacketEquiv Q q).val := rfl

/-- Local angular multiplicity bounds the number of occupied rows in a
selected tree, independent of its original ambient labels. -/
theorem selectedFamily_card_le_local (Q : Finset P.PacketIndex) (w t cone : ℝ)
    (hw : 0<w) (M K : ℕ) (hK : cone≤K)
    (hcone : ∀ q∈Q, |P.rowSlope q.1 q.2.1-t|≤cone*(w/P.length q.1))
    (j : Fin N)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => P.rowSlope j l) (w/P.length j) M) :
    ((P.selectedFamily Q).labels j).card≤(2*K+1)*M := by
  let f : (P.selectedFamily Q).labels j → P.labels j := P.selectedOriginalLabel Q j
  let S := SourceSlopeLabels.window Finset.univ (fun l : P.labels j => P.rowSlope j l)
    t (w/P.length j) cone
  have hf : Set.MapsTo f (Finset.univ : Finset ((P.selectedFamily Q).labels j)) S := by
    intro l _
    obtain ⟨u,hu⟩ := P.selectedLabel_has_packet Q j l
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcone ⟨j,⟨f l,u⟩⟩ hu⟩
  have hinj : Set.InjOn f (Finset.univ : Finset ((P.selectedFamily Q).labels j)) := by
    intro l _ m _ h
    exact Subtype.ext (congrArg (fun a : P.labels j => a.val) h)
  have hc := Finset.card_le_card_of_injOn f hf hinj
  have hb := SourceSlopeLabels.window_card_le Finset.univ
    (fun l : P.labels j => P.rowSlope j l) (t:=t) (div_pos hw (P.length_pos j)) hlocal hK
  simpa only [Finset.card_univ,Fintype.card_coe] using hc.trans hb

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

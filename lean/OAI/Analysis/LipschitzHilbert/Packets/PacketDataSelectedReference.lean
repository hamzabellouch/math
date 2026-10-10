import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCoefficient
import OAI.Analysis.LipschitzHilbert.Geometry.PacketDataReferenceSelection

namespace OAI

/-! A selected tree from an unrestricted packet lattice has a genuine
bounded reference lattice. Only the selected packets are present, and
their original physical waves are preserved. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex)

def selectedLabels (j : Fin N) : Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ (h : l∈P.labels j) (u : Item j l),
    (⟨j,⟨⟨l,h⟩,u⟩⟩ : P.PacketIndex)∈S)

def selectedOriginalLabel (j : Fin N) (l : P.selectedLabels S j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

def SelectedItem (j : Fin N) (l : Label j) :=
  {u : Item j l // ∃ h : l∈P.labels j, (⟨j,⟨⟨l,h⟩,u⟩⟩ : P.PacketIndex)∈S}

instance selectedItemFintype (j : Fin N) (l : Label j) : Fintype (P.SelectedItem S j l) :=
  inferInstanceAs (Fintype {u : Item j l // ∃ h : l∈P.labels j,
    (⟨j,⟨⟨l,h⟩,u⟩⟩ : P.PacketIndex)∈S})

theorem selectedLabel_has_packet (j : Fin N) (l : P.selectedLabels S j) :
    ∃ u : Item j l, (⟨j,⟨P.selectedOriginalLabel S j l,u⟩⟩ : P.PacketIndex)∈S := by
  obtain ⟨h,u,hu⟩ := (Finset.mem_filter.mp l.property).2
  exact ⟨u,hu⟩

theorem selectedItem_mem (j : Fin N) (l : P.selectedLabels S j) (u : P.SelectedItem S j l) :
    (⟨j,⟨P.selectedOriginalLabel S j l,u.val⟩⟩ : P.PacketIndex)∈S := by
  obtain ⟨h,hu⟩ := u.property
  exact hu

variable (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)

include hnear in
theorem selectedLabel_near (j : Fin N) (l : P.selectedLabels S j) :
    |P.rowSlope j (P.selectedOriginalLabel S j l)-t|≤Cb*w/P.length j := by
  obtain ⟨u,hu⟩ := P.selectedLabel_has_packet S j l
  exact hnear ⟨j,⟨P.selectedOriginalLabel S j l,u⟩⟩ hu

def selectedReference : SourceLabeledLattice N κ Label (P.SelectedItem S) where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := F*Cb
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := mul_nonneg hF hCb
  labels := P.selectedLabels S
  originX := fun j l => P.originX j (P.selectedOriginalLabel S j l)
  originZ := fun j l => P.originZ j (P.selectedOriginalLabel S j l)-
    t*P.originX j (P.selectedOriginalLabel S j l)
  rowSlope := fun j l => P.rowSlope j (P.selectedOriginalLabel S j l)-t
  frequency := P.frequency
  site := fun j l u => P.site j (P.selectedOriginalLabel S j l) u.val
  site_injective := fun j l => (P.site_injective j (P.selectedOriginalLabel S j l)).comp
    Subtype.val_injective
  profile := fun j l u k => P.profile j (P.selectedOriginalLabel S j l) u.val k
  profile_bound := fun j l u k => P.profile_bound j (P.selectedOriginalLabel S j l) u.val k
  shear_bound := by
    intro j l
    have hr := (le_div_iff₀ (P.length_pos j)).mp (P.selectedLabel_near S t Cb w hnear j l)
    change |(P.rowSlope j (P.selectedOriginalLabel S j l)-t)*P.length j/P.width|≤1
    rw [abs_div,abs_mul,abs_of_pos (P.length_pos j),abs_of_pos P.width_pos]
    exact (div_le_one P.width_pos).mpr (hr.trans hwide)
  carrier_bound := by
    intro j l k
    have hr := (le_div_iff₀ (P.length_pos j)).mp (P.selectedLabel_near S t Cb w hnear j l)
    change |P.frequency k*(P.rowSlope j (P.selectedOriginalLabel S j l)-t)*P.length j|≤F*Cb
    rw [abs_mul,abs_mul,abs_of_pos (P.length_pos j),mul_assoc]
    calc
      _ ≤ (F/w)*(Cb*w) := mul_le_mul (hfrequency k) hr
        (mul_nonneg (abs_nonneg _) (P.length_pos j).le) (div_nonneg hF hw.le)
      _ = F*Cb := by field_simp

local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

def selectedReferenceEquiv : (Q).PacketIndex ≃ S where
  toFun := fun q => ⟨⟨q.1,⟨P.selectedOriginalLabel S q.1 q.2.1,q.2.2.val⟩⟩,
    P.selectedItem_mem S q.1 q.2.1 q.2.2⟩
  invFun := fun q => ⟨q.val.1,⟨
    ⟨q.val.2.1.val,Finset.mem_filter.mpr ⟨q.val.2.1.property,
      ⟨q.val.2.1.property,q.val.2.2,q.property⟩⟩⟩,
    ⟨q.val.2.2,⟨q.val.2.1.property,q.property⟩⟩⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem selectedReference_actualX (j : Fin N) (l : (Q).labels j)
    (u : P.SelectedItem S j l) :
    (Q).actualX j l u=P.actualX j (P.selectedOriginalLabel S j l) u.val := rfl

theorem selectedReference_actualZ (j : Fin N) (l : (Q).labels j)
    (u : P.SelectedItem S j l) :
    (Q).actualZ j l u=P.actualZ j (P.selectedOriginalLabel S j l) u.val-
      t*P.actualX j (P.selectedOriginalLabel S j l) u.val := by
  dsimp [SourceLabeledLattice.actualZ,SourceLabeledLattice.actualX,actualX,actualZ,
    selectedReference,SourceLabeledLattice.length,length]
  ring

theorem selectedReference_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : P.SelectedItem S j l) (k : κ) :
    (Q).physicalPacket t j l u k=P.physicalPacket 0 j (P.selectedOriginalLabel S j l) u.val k := by
  have hx := P.selectedReference_actualX S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  have hz := P.selectedReference_actualZ S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx,hz]
  change physicalPlanarPacket (P.profile j (P.selectedOriginalLabel S j l) u.val k)
    (P.actualX j (P.selectedOriginalLabel S j l) u.val)
    (P.actualZ j (P.selectedOriginalLabel S j l) u.val-
      t*P.actualX j (P.selectedOriginalLabel S j l) u.val+
      t*P.actualX j (P.selectedOriginalLabel S j l) u.val)
    (P.length j) P.width (t+(P.rowSlope j (P.selectedOriginalLabel S j l)-t))
    (P.frequency k) (P.length_pos j).ne' P.width_pos.ne' = _
  have hs : t+(P.rowSlope j (P.selectedOriginalLabel S j l)-t)=
      P.rowSlope j (P.selectedOriginalLabel S j l) := by ring
  rw [sub_add_cancel,hs]
  simp only [zero_mul,add_zero,zero_add]


theorem selectedReference_sum {E : Type*} [AddCommMonoid E] (f : P.PacketIndex → E) :
    (∑ r : (Q).PacketIndex,
      f (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear r).val) =
        ∑ q∈S, f q := by
  have h := Equiv.sum_comp
    (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear)
    (fun q : S => f q.val)
  exact h.trans (Finset.sum_subtype S (p := fun q => q∈S) (by simp) f).symm

theorem selectedReference_card (M R : ℕ) (hR : Cb≤R)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M) (j : Fin N) :
    ((Q).labels j).card≤(2*R+1)*M := by
  let W := SourceSlopeLabels.window Finset.univ (P.rowSlope j) t (w/P.length j) Cb
  let embed : P.selectedLabels S j ↪ W :=
    { toFun := fun l => ⟨P.selectedOriginalLabel S j l,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,by
          simpa only [mul_div_assoc] using P.selectedLabel_near S t Cb w hnear j l⟩⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : W => z.val.val) hab }
  have hcount : (P.selectedLabels S j).card≤W.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective embed embed.injective
  exact hcount.trans (SourceSlopeLabels.window_card_le Finset.univ (P.rowSlope j)
    (div_pos hw (P.length_pos j)) (hlocal j) hR)

end LipschitzHilbert.PacketLatticeData

end

end OAI

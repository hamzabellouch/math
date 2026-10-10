import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensity

namespace OAI

/-! Drop a finite initial scale segment without changing any physical
packet in the remaining dyadic family. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def dropIndex (first : Fin N) (j : Fin (N-first.val)) : Fin N :=
  ⟨first.val+j.val,by have := j.isLt; have := first.isLt; omega⟩

theorem drop_length (first : Fin N) (j : Fin (N-first.val)) :
    P.length first/(2:ℝ)^j.val=P.length (dropIndex first j) := by
  unfold length dropIndex
  rw [pow_add,div_div]

def dropScales (first : Fin N) :
    PacketLatticeData (N-first.val) κ (fun j => Label (dropIndex first j))
      (fun j l => Item (dropIndex first j) l) where
  topLength := P.length first
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.length_pos first
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  labels := fun j => P.labels (dropIndex first j)
  originX := fun j => P.originX (dropIndex first j)
  originZ := fun j => P.originZ (dropIndex first j)
  rowSlope := fun j => P.rowSlope (dropIndex first j)
  frequency := P.frequency
  site := fun j => P.site (dropIndex first j)
  site_injective := fun j => P.site_injective (dropIndex first j)
  profile := fun j => P.profile (dropIndex first j)
  profile_bound := fun j => P.profile_bound (dropIndex first j)

@[simp] theorem dropScales_length (first : Fin N) (j : Fin (N-first.val)) :
    (P.dropScales first).length j=P.length (dropIndex first j) := P.drop_length first j

@[simp] theorem dropScales_physicalPacket (first : Fin N) (t : ℝ)
    (j : Fin (N-first.val)) (l : (P.dropScales first).labels j)
    (u : Item (dropIndex first j) l) (k : κ) :
    (P.dropScales first).physicalPacket t j l u k=P.physicalPacket t (dropIndex first j) l u k := by
  unfold physicalPacket actualX actualZ
  simp only [dropScales_length]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI

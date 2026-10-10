import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceConditions
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedSum

namespace OAI

/-! Assigned top restrictions with common label and item types. The top
is part of the label, so each top family contains exactly its own packets
and the family-valued concentration and path estimates apply literally. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def AssignedTopItem (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (j : Fin N) (l : τ×P.labels j) :=
  {u : Item j l.2 // (⟨j,⟨l.2,u⟩⟩ : P.PacketIndex) ∈ packets ∧
    assigned ⟨j,⟨l.2,u⟩⟩ = l.1}

instance assignedTopItemFintype (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (j : Fin N) (l : τ×P.labels j) : Fintype (P.AssignedTopItem packets assigned j l) := by
  unfold AssignedTopItem
  infer_instance

def assignedTopFamily (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ) :
    PacketLatticeData N κ (fun j => τ×P.labels j) (P.AssignedTopItem packets assigned) where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  labels := fun j => {top} ×ˢ (Finset.univ : Finset (P.labels j))
  originX := fun j l => P.originX j l.val.2
  originZ := fun j l => P.originZ j l.val.2
  rowSlope := fun j l => P.rowSlope j l.val.2
  frequency := P.frequency
  site := fun j l u => P.site j l.val.2 u.val
  site_injective := fun j l => (P.site_injective j l.val.2).comp Subtype.val_injective
  profile := fun j l u k => P.profile j l.val.2 u.val k
  profile_bound := fun j l u k => P.profile_bound j l.val.2 u.val k

@[simp] theorem assignedTopFamily_length (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (top : τ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).length j = P.length j := rfl

@[simp] theorem assignedTopFamily_label_count (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (top : τ) (j : Fin N) :
    ((P.assignedTopFamily packets assigned top).labels j).card = (P.labels j).card := by
  simp [assignedTopFamily]

/-- No packet is copied to a second top, and no empty fiber adds a packet. -/
def assignedTopPacketEquiv (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (top : τ) : (P.assignedTopFamily packets assigned top).PacketIndex ≃
      packets.filter (fun q => assigned q = top) where
  toFun := fun q => ⟨⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩,by
    apply Finset.mem_filter.mpr
    refine ⟨q.2.2.property.1,?_⟩
    have ht : q.2.1.val.1 = top :=
      Finset.mem_singleton.mp (Finset.mem_product.mp q.2.1.property).1
    exact q.2.2.property.2.trans ht⟩
  invFun := fun q => ⟨q.val.1,⟨⟨(top,q.val.2.1),by
    simp only [assignedTopFamily,Finset.mem_product,Finset.mem_singleton,
      Finset.mem_univ,and_self]⟩,
    ⟨q.val.2.2,(Finset.mem_filter.mp q.property).1,(Finset.mem_filter.mp q.property).2⟩⟩⟩
  left_inv := by
    rintro ⟨j,⟨⟨⟨s,l⟩,hl⟩,⟨u,hu⟩⟩⟩
    have hs : s = top := Finset.mem_singleton.mp (Finset.mem_product.mp hl).1
    subst s
    rfl
  right_inv := by
    intro q
    rfl

theorem assignedTopFamily_physicalPacket (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (top : τ) (t : ℝ) (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) :
    (P.assignedTopFamily packets assigned top).physicalPacket t j l u k =
      P.physicalPacket t j l.val.2 u.val k := rfl

/-- Repartitioning retains the original analyzing integral exactly. -/
theorem assignedTopFamily_physicalMultiplierCoefficient (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (P.assignedTopFamily packets assigned top).physicalMultiplierCoefficient t
      (fun j l => b j l.val.2) v f j l u =
      P.physicalMultiplierCoefficient t b v f j l.val.2 u.val := rfl

theorem sum_assignedTopPackets {E : Type*} [AddCommMonoid E]
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
    (f : P.PacketIndex → E) :
    (∑ q : (P.assignedTopFamily packets assigned top).PacketIndex,
      f ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩) =
      ∑ q ∈ packets.filter (fun q => assigned q = top), f q := by
  have h := Equiv.sum_comp (P.assignedTopPacketEquiv packets assigned top)
    (fun q => f q.val)
  exact h.trans (Finset.sum_subtype _ (p := fun q =>
    q ∈ packets.filter (fun q => assigned q = top)) (by simp) f).symm

end LipschitzHilbert.PacketLatticeData

end

end OAI

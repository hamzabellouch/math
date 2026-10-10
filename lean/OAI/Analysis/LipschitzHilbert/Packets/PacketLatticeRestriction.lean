import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeData
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI

/-! Exact label restriction and finite tag partitions for the unrestricted
packet family. Neither operation changes a packet or a lattice site. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def restrictedLabels (keep : ∀ j, P.labels j → Prop) (j : Fin N) : Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ h : l∈P.labels j, keep j ⟨l,h⟩)

def restrictedOriginalLabel (keep : ∀ j, P.labels j → Prop) (j : Fin N)
    (l : P.restrictedLabels keep j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

theorem restrictedLabel_kept (keep : ∀ j, P.labels j → Prop) (j : Fin N)
    (l : P.restrictedLabels keep j) : keep j (P.restrictedOriginalLabel keep j l) := by
  obtain ⟨h,hkeep⟩ := (Finset.mem_filter.mp l.property).2
  exact hkeep

def restrictedLabelEquiv (keep : ∀ j, P.labels j → Prop) (j : Fin N) :
    P.restrictedLabels keep j ≃ {l : P.labels j // keep j l} where
  toFun := fun l => ⟨P.restrictedOriginalLabel keep j l,P.restrictedLabel_kept keep j l⟩
  invFun := fun l => ⟨l.val.val,Finset.mem_filter.mpr ⟨l.val.property,⟨l.val.property,l.property⟩⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext (Subtype.ext rfl)

def restrictLabels (keep : ∀ j, P.labels j → Prop) : PacketLatticeData N κ Label Item :=
  { P with
    labels := P.restrictedLabels keep
    originX := fun j l => P.originX j (P.restrictedOriginalLabel keep j l)
    originZ := fun j l => P.originZ j (P.restrictedOriginalLabel keep j l)
    rowSlope := fun j l => P.rowSlope j (P.restrictedOriginalLabel keep j l)
    site := fun j l => P.site j (P.restrictedOriginalLabel keep j l)
    site_injective := fun j l => P.site_injective j (P.restrictedOriginalLabel keep j l)
    profile := fun j l => P.profile j (P.restrictedOriginalLabel keep j l)
    profile_bound := fun j l => P.profile_bound j (P.restrictedOriginalLabel keep j l) }

@[simp] theorem restrictLabels_physicalPacket (keep : ∀ j, P.labels j → Prop)
    (t : ℝ) (j : Fin N) (l : (P.restrictLabels keep).labels j) (u : Item j l) (k : κ) :
    (P.restrictLabels keep).physicalPacket t j l u k =
      P.physicalPacket t j (P.restrictedOriginalLabel keep j l) u k := rfl

@[simp] theorem restrictLabels_length (keep : ∀ j, P.labels j → Prop) (j : Fin N) :
    (P.restrictLabels keep).length j = P.length j := rfl

theorem restrictedLabels_card_le (keep : ∀ j, P.labels j → Prop) (j : Fin N) :
    (P.restrictedLabels keep j).card ≤ (P.labels j).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

variable {Tag : Type*} [Fintype Tag] (tag : ∀ j, P.labels j → Tag)

def tagLabelEquiv (j : Fin N) :
    (Σ g : Tag, P.restrictedLabels (fun i l => tag i l=g) j) ≃ P.labels j :=
  (Equiv.sigmaCongrRight (fun g => P.restrictedLabelEquiv (fun i l => tag i l=g) j)).trans
    (Equiv.sigmaFiberEquiv (tag j))

omit [Fintype Tag] in
@[simp] theorem tagLabelEquiv_apply (j : Fin N) (g : Tag)
    (l : P.restrictedLabels (fun i a => tag i a=g) j) :
    P.tagLabelEquiv tag j ⟨g,l⟩ =
      P.restrictedOriginalLabel (fun i a => tag i a=g) j l := rfl

/-- The partition has exactly one copy of each original term, including
arbitrary empty label fibers and empty spatial item types. -/
theorem sum_tag_restrictions {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E) :
    (∑ g : Tag, ∑ l : (P.restrictLabels (fun i a => tag i a=g)).labels j,
      ∑ u : Item j l, f (P.restrictedOriginalLabel (fun i a => tag i a=g) j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have h := Equiv.sum_comp (P.tagLabelEquiv tag j)
    (fun l : P.labels j => ∑ u : Item j l, f l u)
  simp only [Fintype.sum_sigma] at h
  dsimp only [tagLabelEquiv,Equiv.trans_apply,Equiv.sigmaCongrRight,
    Equiv.sigmaFiberEquiv,restrictedLabelEquiv] at h
  exact h

/-- Replacing the analyzing profile keeps all physical geometry. -/
def withProfile (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound) :
    PacketLatticeData N κ Label Item :=
  { P with profile := alt, profile_bound := hAlt }

end LipschitzHilbert.PacketLatticeData

end

end OAI

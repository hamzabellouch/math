import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceUnion
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledStoppingVariation

namespace OAI

/-! Any fixed residual packet subset is itself a lattice family, with
unchanged geometry, analyzing integrals and alternate synthesis waves.
Restricting the item fibers preserves the lattice constants exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def RestrictedPacketItem (Q : Finset P.PacketIndex) (j : Fin N) (l : Label j) :=
  {u : Item j l // ∃ h : l ∈ P.labels j, (⟨j,⟨⟨l,h⟩,u⟩⟩ : P.PacketIndex) ∈ Q}

instance restrictedPacketItemFintype (Q : Finset P.PacketIndex) (j : Fin N) (l : Label j) :
    Fintype (P.RestrictedPacketItem Q j l) := by
  unfold RestrictedPacketItem
  infer_instance

def restrictPackets (Q : Finset P.PacketIndex) :
    SourceLabeledLattice N κ Label (P.RestrictedPacketItem Q) :=
  P.referenceItems (P.RestrictedPacketItem Q)
    (fun j l u => P.site j l u.val)
    (fun j l => (P.site_injective j l).comp Subtype.val_injective)
    (fun j l u k => P.profile j l u.val k)
    (fun j l u k => P.profile_bound j l u.val k)

@[simp] theorem restrictPackets_absoluteConstant (Q : Finset P.PacketIndex) :
    (P.restrictPackets Q).absoluteConstant = P.absoluteConstant := rfl

@[simp] theorem restrictPackets_constant (Q : Finset P.PacketIndex) :
    (P.restrictPackets Q).constant = P.constant := rfl

/-- The restricted packet type is precisely the selected finite set. -/
def restrictedPacketEquiv (Q : Finset P.PacketIndex) :
    (P.restrictPackets Q).PacketIndex ≃ Q where
  toFun := fun q => ⟨⟨q.1,⟨q.2.1,q.2.2.val⟩⟩,by
    obtain ⟨h,hm⟩ := q.2.2.property
    exact hm⟩
  invFun := fun q => ⟨q.val.1,⟨q.val.2.1,⟨q.val.2.2,⟨q.val.2.1.property,q.property⟩⟩⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem restrictPackets_physicalPacket (Q : Finset P.PacketIndex) (t : ℝ)
    (j : Fin N) (l : (P.restrictPackets Q).labels j) (u : P.RestrictedPacketItem Q j l) (k : κ) :
    (P.restrictPackets Q).physicalPacket t j l u k = P.physicalPacket t j l u.val k := rfl

@[simp] theorem restrictPackets_physicalMultiplierCoefficient (Q : Finset P.PacketIndex)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N)
    (l : (P.restrictPackets Q).labels j) (u : P.RestrictedPacketItem Q j l) :
    (P.restrictPackets Q).physicalMultiplierCoefficient t b v g j l u =
      P.physicalMultiplierCoefficient t b v g j l u.val := rfl

/-- Exact scalar/vector sums over the selected packet family. -/
theorem sum_restrictPackets {E : Type*} [AddCommMonoid E] (Q : Finset P.PacketIndex)
    (f : P.PacketIndex → E) :
    (∑ q : (P.restrictPackets Q).PacketIndex, f ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩) =
      ∑ q ∈ Q, f q := by
  have h := Equiv.sum_comp (P.restrictedPacketEquiv Q) (fun q : Q => f q.val)
  exact h.trans (Finset.sum_subtype Q (p := fun q => q ∈ Q) (by simp) f).symm

theorem sum_restrictPackets_filter {E : Type*} [AddCommMonoid E] (Q : Finset P.PacketIndex)
    (f : P.PacketIndex → E) (keep : P.PacketIndex → Prop) :
    (∑ q ∈ Finset.univ.filter (fun q : (P.restrictPackets Q).PacketIndex =>
      keep ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩), f ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩) =
      ∑ q ∈ Q.filter keep, f q := by
  simp only [Finset.sum_filter]
  exact P.sum_restrictPackets Q (fun q => if keep q then f q else 0)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- Alternate synthesis profiles are restricted along the same item map. -/
def restrictedAlternate (Q : Finset P.PacketIndex) (j : Fin N)
    (l : (P.restrictPackets Q).labels j) (u : P.RestrictedPacketItem Q j l) (k : κ) :
    SchwartzMap (ℝ×ℝ) ℂ := alt j l u.val k

include hAlt in
theorem restrictedAlternate_bound (Q : Finset P.PacketIndex) (j : Fin N)
    (l : (P.restrictPackets Q).labels j) (u : P.RestrictedPacketItem Q j l) (k : κ) :
    planarProfileConstant (P.restrictedAlternate alt Q j l u k)
      (2*(P.restrictPackets Q).order) ≤ (P.restrictPackets Q).profileBound :=
  hAlt j l u.val k

theorem restrictPackets_physicalMaskedValue (Q : Finset P.PacketIndex)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (q : (P.restrictPackets Q).PacketIndex) :
    (P.restrictPackets Q).physicalMaskedValue (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val) L A z q =
      P.physicalMaskedValue alt hAlt t b v g T L A z ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩ := rfl

/-- Every fixed selected length-band is the corresponding band of the
literal restricted family, with the original analyzing coefficient. -/
theorem restrictPackets_physicalMaskedBand (Q : Finset P.PacketIndex)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y x : ℝ) (j : Fin N) :
    (P.restrictPackets Q).physicalMaskedBand (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val) L A y j x =
      ∑ q ∈ Q.filter (fun q => q.1 = j),
        P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q := by
  rw [← (P.restrictPackets Q).physicalMaskedValue_length_sum
    (P.restrictedAlternate alt Q) (P.restrictedAlternate_bound alt hAlt Q)
    t b v g (fun j l u => T j l u.val) L A y x j]
  simp_rw [P.restrictPackets_physicalMaskedValue alt hAlt Q]
  ext k
  simp only [WithLp.ofLp_sum,Finset.sum_apply]
  convert P.sum_restrictPackets_filter Q
    (fun q => P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q k)
    (fun q => q.1 = j) using 1 <;> congr 1 <;> ext q <;> simp

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

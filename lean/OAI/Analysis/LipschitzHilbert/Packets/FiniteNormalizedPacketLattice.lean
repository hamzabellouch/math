import OAI.Analysis.LipschitzHilbert.Packets.FinitePacketSites
import OAI.Analysis.LipschitzHilbert.Packets.NormalizedPacketKernelForm
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataLatticeSites

namespace OAI

/-! Realization of an arbitrary finite part of the translated lattice
by the actual normalized packet data. The site fibers are shared by
all carrier components and add no extra terms. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]
variable (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1≤ratioBound) (hscale : |scale/width|≤ratioBound)
  (labels : ∀ j, Finset (Label j))
  (origin : ∀ j, labels j → ℝ×ℝ) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (S : Finset (LatticeSiteIndex labels))
  (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order)≤C)

attribute [local instance] Classical.propDecidable

def finiteSiteFiber (j : Fin N) (l : Label j) : Finset (ℤ×ℤ) :=
  if h : l∈labels j then retainedSites labels S j ⟨l,h⟩ else ∅

def finiteSiteFiberEquiv (j : Fin N) (l : labels j) :
    finiteSiteFiber labels S j l.val ≃ retainedSites labels S j l :=
  Equiv.subtypeEquivRight (by
    intro n
    simp [finiteSiteFiber,l.property])

def finiteNormalizedPacketLattice : PacketLatticeData N κ Label
    (fun j l => finiteSiteFiber labels S j l) :=
  normalizedPacketLattice F q nu topLength width scale ratioBound C order
    htop hwidth hC horder hratio hscale labels (fun j l => (origin j l).1)
    (fun j l => (origin j l).2) theta center (fun _ _ n => n.val)
    (fun _ _ => Subtype.val_injective) hprofile

local notation "P" => finiteNormalizedPacketLattice F q nu topLength width scale ratioBound C order
  htop hwidth hC horder hratio hscale labels origin theta center S hprofile

def finiteNormalizedPacketEquiv : (P).PacketIndex ≃ S :=
  (Equiv.sigmaCongrRight (fun j => Equiv.sigmaCongrRight
    (fun l : labels j => finiteSiteFiberEquiv labels S j l))).trans
      (retainedSiteEquiv labels S)

theorem finiteNormalizedPacketEquiv_apply (s : (P).PacketIndex) :
    (finiteNormalizedPacketEquiv F q nu topLength width scale ratioBound C order
      htop hwidth hC horder hratio hscale labels origin theta center S hprofile s).val =
        ⟨s.1,⟨s.2.1,s.2.2.val⟩⟩ := rfl

theorem finiteNormalizedPacket_sum {E : Type*} [AddCommMonoid E]
    (f : LatticeSiteIndex labels → E) :
    (∑ s : (P).PacketIndex, f ⟨s.1,⟨s.2.1,s.2.2.val⟩⟩) = ∑ s∈S, f s := by
  have h := Equiv.sum_comp
    (finiteNormalizedPacketEquiv F q nu topLength width scale ratioBound C order
      htop hwidth hC horder hratio hscale labels origin theta center S hprofile)
    (fun s : S => f s.val)
  exact h.trans (Finset.sum_subtype S (p := fun s => s∈S) (by simp) f).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI

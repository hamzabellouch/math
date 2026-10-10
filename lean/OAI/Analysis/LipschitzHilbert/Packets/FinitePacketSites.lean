import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

namespace OAI

/-! Any finite collection in the joint spatial lattice is realized by
finite site fibers. No rectangular truncation or extra packet is added. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {Label : Fin N → Type} (labels : ∀ j, Finset (Label j))

abbrev LatticeSiteIndex := Σ j : Fin N, Σ _l : labels j, ℤ×ℤ

abbrev LatticeRow := Σ j : Fin N, labels j

def latticeSiteProductEquiv : LatticeSiteIndex labels ≃ (LatticeRow labels × (ℤ×ℤ)) where
  toFun := fun s => (⟨s.1,s.2.1⟩,s.2.2)
  invFun := fun s => ⟨s.1.1,⟨s.1.2,s.2⟩⟩
  left_inv := by intro s; rfl
  right_inv := by intro s; rfl

theorem sum_joint_lattice_sites {E : Type*} [AddCommMonoid E]
    (S : Finset (LatticeRow labels × (ℤ×ℤ))) (f : LatticeSiteIndex labels → E) :
    (∑ s∈S.map (latticeSiteProductEquiv labels).symm.toEmbedding, f s) =
      ∑ p∈S, f ((latticeSiteProductEquiv labels).symm p) :=
  Finset.sum_map _ _ _

private theorem siteIndex_injective (j : Fin N) (l : labels j) :
    Function.Injective (fun n : ℤ×ℤ => (⟨j,⟨l,n⟩⟩ : LatticeSiteIndex labels)) := by
  intro a b h
  simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h

def retainedSites (S : Finset (LatticeSiteIndex labels)) (j : Fin N) (l : labels j) :
    Finset (ℤ×ℤ) :=
  S.preimage (fun n => ⟨j,⟨l,n⟩⟩) (siteIndex_injective labels j l).injOn

theorem mem_retainedSites (S : Finset (LatticeSiteIndex labels))
    (j : Fin N) (l : labels j) (n : ℤ×ℤ) :
    n∈retainedSites labels S j l ↔ (⟨j,⟨l,n⟩⟩ : LatticeSiteIndex labels)∈S :=
  Finset.mem_preimage

def retainedSiteEquiv (S : Finset (LatticeSiteIndex labels)) :
    (Σ j : Fin N, Σ l : labels j, retainedSites labels S j l) ≃ S where
  toFun := fun q => ⟨⟨q.1,⟨q.2.1,q.2.2.val⟩⟩,
    (mem_retainedSites labels S q.1 q.2.1 q.2.2.val).mp q.2.2.property⟩
  invFun := fun q => ⟨q.val.1,⟨q.val.2.1,⟨q.val.2.2,
    (mem_retainedSites labels S q.val.1 q.val.2.1 q.val.2.2).mpr q.property⟩⟩⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl

theorem sum_retainedSites {E : Type*} [AddCommMonoid E]
    (S : Finset (LatticeSiteIndex labels)) (f : LatticeSiteIndex labels → E) :
    (∑ j, ∑ l : labels j, ∑ n : retainedSites labels S j l, f ⟨j,⟨l,n.val⟩⟩) =
      ∑ q∈S, f q := by
  have h := Equiv.sum_comp (retainedSiteEquiv labels S) (fun q : S => f q.val)
  simp only [Fintype.sum_sigma] at h
  exact h.trans (Finset.sum_subtype S (p := fun q => q∈S) (by simp) f).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI

import OAI.Analysis.LipschitzHilbert.Trees.SourceScaleRestrictionSums
import OAI.Analysis.LipschitzHilbert.Trees.SourceDropDensity

namespace OAI

/-! Exact finite packet subsets after dropping an initial scale segment. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def dropPacket (first : Fin N) (q : (P.dropScales first).PacketIndex) : P.PacketIndex :=
  ⟨dropIndex first q.1,⟨q.2.1,q.2.2⟩⟩

def dropPackets (first : Fin N) (Q : Finset P.PacketIndex) :
    Finset (P.dropScales first).PacketIndex :=
  Finset.univ.filter (fun q => P.dropPacket first q∈Q)

@[simp] theorem mem_dropPackets (first : Fin N) (Q : Finset P.PacketIndex)
    (q : (P.dropScales first).PacketIndex) :
    q∈P.dropPackets first Q ↔ P.dropPacket first q∈Q := by
  simp only [dropPackets,Finset.mem_filter,Finset.mem_univ,true_and]

theorem sum_dropPackets {E : Type*} [AddCommMonoid E]
    (first : Fin N) (Q : Finset P.PacketIndex)
    (hQ : ∀ q∈Q, first.val≤q.1.val) (f : P.PacketIndex → E) :
    (∑ q∈P.dropPackets first Q, f (P.dropPacket first q))=∑ q∈Q, f q := by
  classical
  have h := P.sum_dropScales first (fun j l u =>
    if (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈Q then f ⟨j,⟨l,u⟩⟩ else 0)
  calc
    _ = ∑ j∈Finset.univ.filter (fun j : Fin N => first.val≤j.val),
        ∑ l : P.labels j, ∑ u : Item j l,
          if (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈Q then f ⟨j,⟨l,u⟩⟩ else 0 := by
      rw [dropPackets,Finset.sum_filter]
      simp only [Fintype.sum_sigma,dropPacket]
      exact h
    _ = ∑ j : Fin N, ∑ l : P.labels j, ∑ u : Item j l,
        if (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈Q then f ⟨j,⟨l,u⟩⟩ else 0 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hn
      apply Finset.sum_eq_zero
      intro l _
      apply Finset.sum_eq_zero
      intro u _
      apply ite_eq_right
      intro hmem
      exact hn (Finset.mem_filter.mpr ⟨hj,hQ ⟨j,⟨l,u⟩⟩ hmem⟩)
    _ = ∑ q : P.PacketIndex, if q∈Q then f q else 0 := by simp only [Fintype.sum_sigma]
    _ = _ := by rw [←Finset.sum_filter]; simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

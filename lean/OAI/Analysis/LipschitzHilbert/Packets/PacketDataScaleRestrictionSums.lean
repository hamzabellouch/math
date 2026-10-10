import OAI.Analysis.LipschitzHilbert.Packets.PacketDataScaleRestriction

namespace OAI

/-! Dropping an initial scale segment is an exact reindexing of finite
packet sums. Original coefficients and physical packets are retained. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem dropIndex_injective (first : Fin N) : Function.Injective (dropIndex first) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  change first.val+i.val=first.val+j.val at h
  omega

theorem dropIndex_surjective_tail (first j : Fin N) (hj : first.val≤j.val) :
    ∃ i : Fin (N-first.val), dropIndex first i=j := by
  refine ⟨⟨j.val-first.val,by have := j.isLt; omega⟩,?_⟩
  apply Fin.ext
  change first.val+(j.val-first.val)=j.val
  omega

theorem sum_dropIndex {E : Type*} [AddCommMonoid E] (first : Fin N) (f : Fin N → E) :
    (∑ j : Fin (N-first.val), f (dropIndex first j))=
      ∑ j∈Finset.univ.filter (fun j : Fin N => first.val≤j.val), f j := by
  apply Finset.sum_bij (fun j _ => dropIndex first j)
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp [dropIndex]; omega⟩
  · intro i _ j _ hij
    exact dropIndex_injective first hij
  · intro j hj
    obtain ⟨i,hi⟩ := dropIndex_surjective_tail first j (Finset.mem_filter.mp hj).2
    exact ⟨i,Finset.mem_univ _,hi⟩
  · intro j _
    rfl

theorem sum_dropScales {E : Type*} [AddCommMonoid E] (first : Fin N)
    (f : ∀ j (l : P.labels j), Item j l → E) :
    (∑ j : Fin (N-first.val), ∑ l : (P.dropScales first).labels j,
      ∑ u : Item (dropIndex first j) l, f (dropIndex first j) l u)=
    ∑ j∈Finset.univ.filter (fun j : Fin N => first.val≤j.val),
      ∑ l : P.labels j, ∑ u : Item j l, f j l u :=
  sum_dropIndex first (fun j => ∑ l : P.labels j, ∑ u : Item j l, f j l u)

end LipschitzHilbert.PacketLatticeData

end

end OAI

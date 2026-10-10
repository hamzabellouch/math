import OAI.Analysis.LipschitzHilbert.Trees.SourceScaleRestriction
import OAI.Analysis.LipschitzHilbert.Trees.SourceLongTreeSplit

namespace OAI

/-! Dropping an initial scale segment is an exact reindexing of finite
packet sums. Original coefficients and physical packets are retained. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
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

/-- The full selector sum is unchanged when all omitted coefficients are zero. -/
theorem dropScales_selector_value (first : Fin N) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hz : ∀ j, j.val<first.val → ∀ l u, c j l u=0)
    (selector : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) :
    (P.dropScales first).physicalTreeSelectorValue t
      (fun j l u => c (dropIndex first j) l u)
      (fun j l k => selector (dropIndex first j) l k) z=
      P.physicalTreeSelectorValue t c selector z := by
  unfold physicalTreeSelectorValue
  simp only [dropScales_physicalPacket]
  apply (P.sum_dropScales first (fun j l u => WithLp.toLp 2
    (fun k => c j l u k*selector j l k*P.physicalPacket t j l u k z))).trans
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  have hlt : j.val<first.val := by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hj
  simp only [hz j hlt,WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
  change (∑ _l : P.labels j, ∑ _u : Item j _l, (0 : EuclideanSpace ℂ κ))=0
  simp only [Finset.sum_const_zero]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

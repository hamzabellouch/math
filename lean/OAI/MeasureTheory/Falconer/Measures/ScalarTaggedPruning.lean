import OAI.MeasureTheory.Falconer.Estimates.ScalarInitialDyadic

namespace OAI

/-! Selecting a common geometric tag while retaining whole child fibers.
 The loss is the number of tags times the local pruning loss. -/
namespace Falconer

 theorem scalar_tagged_child_pruning {ι α τ : Type*} [DecidableEq ι] [DecidableEq α] [DecidableEq τ]
    (P : Finset ι) (hP : P.Nonempty) (C F : ι → Finset α) (tag : ι → τ)
    (D H : ℕ) (hF : ∀ p ∈ P, F p ⊆ C p)
    (hd : (P : Set ι).PairwiseDisjoint C)
    (hkeep : ∀ p ∈ P, (C p).card ≤ D*(F p).card)
    (htags : (P.image tag).card ≤ H) :
    ∃ t ∈ P.image tag, (P.biUnion C).card ≤
      D*H*((P.filter fun p => tag p = t).biUnion F).card := by
  classical
  let T := P.image tag
  let w := fun t => ∑ p ∈ P.filter (fun p => tag p = t), (F p).card
  obtain ⟨t,ht,hmax⟩ := T.exists_max_image w (hP.image tag)
  have hFd : (P : Set ι).PairwiseDisjoint F := by
    intro p hp q hq hpq
    exact (hd hp hq hpq).mono (hF p hp) (hF q hq)
  have hsubset : (P.filter fun p => tag p = t : Finset ι) ⊆ P := Finset.filter_subset _ _
  have hv : ((P.filter fun p => tag p = t).biUnion F).card = w t := by
    apply Finset.card_biUnion
    intro p hp q hq hpq
    exact hFd (hsubset hp) (hsubset hq) hpq
  have hsum : (∑ p ∈ P, (F p).card) = ∑ t ∈ T, w t := by
    exact (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem tag hp) _).symm
  refine ⟨t,ht,?_⟩
  rw [hv]
  calc
    (P.biUnion C).card = ∑ p ∈ P, (C p).card := Finset.card_biUnion hd
    _ ≤ ∑ p ∈ P, D*(F p).card := Finset.sum_le_sum hkeep
    _ = D*(∑ p ∈ P, (F p).card) := (Finset.mul_sum _ _ _).symm
    _ = D*(∑ t ∈ T, w t) := by rw [hsum]
    _ ≤ D*(∑ _t ∈ T, w t) := Nat.mul_le_mul_left _ (Finset.sum_le_sum hmax)
    _ = D*(T.card*w t) := by simp
    _ ≤ D*(H*w t) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ htags)
    _ = D*H*w t := by ring

 theorem scalar_equal_fiber_card {ι α : Type*} [DecidableEq ι] [DecidableEq α] (P : Finset ι) (C : ι → Finset α)
    (hd : (P : Set ι).PairwiseDisjoint C) (m : ℕ)
    (hc : ∀ p ∈ P, (C p).card = m) : (P.biUnion C).card = P.card*m := by
  classical
  rw [Finset.card_biUnion hd]
  calc
    _ = ∑ _p ∈ P, m := Finset.sum_congr rfl hc
    _ = _ := by simp

end Falconer

end OAI

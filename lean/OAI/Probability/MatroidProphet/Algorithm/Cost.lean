import OAI.Probability.MatroidProphet.Algorithm.Expectation
import OAI.Probability.MatroidProphet.CandidateFilter

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma sum_groupMask_card_le {ι : Type*} (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (J : Finset ι) (idx : ι → ℕ) (hinj : Set.InjOn idx (J : Set ι))
    (mask target : Finset (Fin n))
    (hsub : ∀ j ∈ J, groupMask M d w mask (idx j) ⊆ (target : Set (Fin n))) :
    (∑ j ∈ J, (groupMask M d w mask (idx j)).ncard) ≤ target.card := by
  classical
  let f : ι → Finset (Fin n) := fun j => (groupMask M d w mask (idx j)).toFinset
  have hf (j : ι) : f j ⊆ pathGroups M d w (idx j) := by
    intro e he
    have hx : e ∈ groupMask M d w mask (idx j) := by simpa [f] using he
    have hg : e ∈ groupMask M d w univ (idx j) := ⟨mem_univ _, hx.2⟩
    simpa [pathGroups] using hg
  have hd : (J : Set ι).PairwiseDisjoint f := by
    intro i hi j hj hij
    have hij' : idx i ≠ idx j := fun heq => hij (hinj hi hj heq)
    exact (pathGroups_disjoint M d w hij').mono (hf i) (hf j)
  have hs : J.biUnion f ⊆ target := by
    intro e he
    obtain ⟨j, hj, hej⟩ := mem_biUnion.mp he
    exact hsub j hj (by simpa [f] using hej)
  have hcard := Finset.card_le_card hs
  rw [card_biUnion hd] at hcard
  simpa only [f, ← Set.ncard_eq_toFinset_card'] using hcard

lemma groupMask_eq_focal (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) {h : ℕ} {i : ℤ}
    (hi : (groups M d w)[h]? = some i) :
    (groupMask M d w mask h).toFinset =
      mask ∩ ((candidateLabels M w d.H).filter (fun e => w e = some i)) := by
  classical
  ext e
  simp only [Set.mem_toFinset, Finset.mem_inter, mem_filter, candidateLabels, candidateSet, Finset.mem_univ, true_and]
  change (e ∈ mask ∧ candidate M d w e (w e) ∧ w e = (groups M d w)[h]?) ↔
    (e ∈ mask ∧ candidate M d w e (w e) ∧ w e = some i)
  simp only [hi]

lemma groupMask_later_subset (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) {h j : ℕ} {i : ℤ}
    (hi : (groups M d w)[h]? = some i) (hj : j < (groups M d w).length) (hhj : h < j) :
    groupMask M d w mask j ⊆
      (mask ∩ ((candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)) :
        Finset (Fin n)) := by
  intro e he
  have hjget : (groups M d w)[j]? = some ((groups M d w)[j]) := List.getElem?_eq_getElem hj
  obtain ⟨k, hk, hkj⟩ := groups_earlier_key M d w hjget hhj
  have hki : k = i := Option.some.inj (hk.symm.trans hi)
  subst k
  exact Finset.mem_inter.mpr ⟨he.1, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, he.2.1⟩,
    _, he.2.2.trans hjget, hkj⟩⟩

theorem listed_cost_le_true_counts (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) {h : ℕ} {i : ℤ} (hi : (groups M d w)[h]? = some i) (κ : ℕ) :
    κ * (groupMask M d w d.C h).ncard +
      ∑ j ∈ range ((groups M d w).length-(h+1)),
        (κ * (groupMask M d w d.C (h+1+j)).ncard +
          (groupMask M d w d.D (h+1+j)).ncard) ≤
    κ * (d.C ∩ ((candidateLabels M w d.H).filter (fun e => w e = some i))).card +
      κ * (d.C ∩ ((candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k))).card +
        ((candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)).card := by
  classical
  let J := range ((groups M d w).length-(h+1))
  let high := (candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)
  have hh := (List.getElem?_eq_some_iff.mp hi).1
  have hc : (∑ j ∈ J, (groupMask M d w d.C (h+1+j)).ncard) ≤ (d.C ∩ high).card := by
    apply sum_groupMask_card_le M d w J (fun j => h+1+j) (by intro a _ b _ hab; change h+1+a = h+1+b at hab; omega)
    intro j hj
    exact groupMask_later_subset M d w d.C hi (by have := mem_range.mp hj; omega) (by omega)
  have hd : (∑ j ∈ J, (groupMask M d w d.D (h+1+j)).ncard) ≤ high.card := by
    apply sum_groupMask_card_le M d w J (fun j => h+1+j) (by intro a _ b _ hab; change h+1+a = h+1+b at hab; omega)
    intro j hj e he
    have hm := groupMask_later_subset M d w d.D hi
      (by have := mem_range.mp hj; omega) (by omega) he
    exact (Finset.mem_inter.mp hm).2
  have hf : (groupMask M d w d.C h).ncard =
      (d.C ∩ ((candidateLabels M w d.H).filter (fun e => w e = some i))).card := by
    rw [Set.ncard_eq_toFinset_card', groupMask_eq_focal M d w d.C hi]
  rw [hf, sum_add_distrib, ← mul_sum]
  have hm := Nat.mul_le_mul_left κ hc
  change _ ≤ _ at hd
  dsimp [J, high] at hm hd
  omega

end MatroidProphet.MainAlgorithm

end OAI

import OAI.Probability.MatroidProphet.Algorithm.Feasible

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

lemma candidate_congr (M : Matroid (Fin n)) (d : MainMasks n)
    (s s' : Fin n → Option ℤ) (h : ∀ e ∈ d.H, s e = s' e) (e : Fin n) (w : Option ℤ) :
    candidate M d s e w ↔ candidate M d s' e w := by
  have heq : {f | f ∈ d.H ∧ higher f (s f) e w} = {f | f ∈ d.H ∧ higher f (s' f) e w} := by
    ext f
    by_cases hf : f ∈ d.H
    · simp only [Set.mem_ofPred_eq, hf, true_and, h f hf]
    · simp [hf]
  simp only [candidate, heq]

lemma listed_congr (M : Matroid (Fin n)) (d : MainMasks n)
    (s s' : Fin n → Option ℤ)
    (hH : ∀ e ∈ d.H, s e = s' e) (hD : ∀ e ∈ d.D, s e = s' e) :
    listed M d s = listed M d s' := by
  classical
  unfold listed
  apply Finset.biUnion_congr rfl
  intro e he
  have hc := candidate_congr M d s s' hH e (s e)
  rw [hD e he] at hc
  simp only [hD e he, hc]

lemma groups_congr (M : Matroid (Fin n)) (d : MainMasks n)
    (s s' : Fin n → Option ℤ)
    (hH : ∀ e ∈ d.H, s e = s' e) (hD : ∀ e ∈ d.D, s e = s' e) :
    groups M d s = groups M d s' := by
  rw [groups, groups, listed_congr M d s s' hH hD]

lemma groupMask_congr (M : Matroid (Fin n)) (d : MainMasks n)
    (s s' : Fin n → Option ℤ) (mask : Finset (Fin n))
    (hH : ∀ e ∈ d.H, s e = s' e) (hD : ∀ e ∈ d.D, s e = s' e)
    (hmask : ∀ e ∈ mask, s e = s' e) :
    groupMask M d s mask = groupMask M d s' mask := by
  funext j
  ext e
  by_cases he : e ∈ mask
  · have hc := candidate_congr M d s s' hH e (s e)
    rw [hmask e he] at hc
    simp only [groupMask, Set.mem_ofPred_eq, he, true_and,
      hmask e he, hc, groups_congr M d s s' hH hD]
  · simp [groupMask, he]

lemma preprocessing_congr (M : Matroid (Fin n)) (hE : M.E = Set.univ) (d : MainMasks n)
    (s s' : Fin n → Option ℤ) (h : ∀ e ∈ d.H ∪ d.D ∪ d.C, s e = s' e) :
    finalPath M hE d s = finalPath M hE d s' ∧
      birth M hE d s = birth M hE d s' ∧ assign M hE d s = assign M hE d s' := by
  classical
  have hH : ∀ e ∈ d.H, s e = s' e := fun e he => h e (mem_union_left _ (mem_union_left _ he))
  have hD : ∀ e ∈ d.D, s e = s' e := fun e he => h e (mem_union_left _ (mem_union_right _ he))
  have hC : ∀ e ∈ d.C, s e = s' e := fun e he => h e (mem_union_right _ he)
  have hgd := groupMask_congr M d s s' d.D hH hD hD
  have hgc := groupMask_congr M d s s' d.C hH hD hC
  have hgs := groups_congr M d s s' hH hD
  have hf : finalPath M hE d s = finalPath M hE d s' := by
    simp only [finalPath, hgd, hgc, hgs]
  have hb : birth M hE d s = birth M hE d s' := by
    funext e i
    simp only [birth, hgd, hgc, hgs]
  refine ⟨hf, hb, ?_⟩
  funext e w
  have hel (i : ℤ) : eligible M hE d s e i ↔ eligible M hE d s' e i := by
    simp only [eligible, hf, hb, hgs, candidate_congr M d s s' hH]
  cases w <;> simp only [assign, hel, hb]

lemma observed_preprocessing (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) :
    let s := fun e => roundedLevel weightBase (observed (hidden M hE) r w e)
    let s' := fun e => roundedLevel weightBase (w e)
    finalPath M hE (mainMasks r) s = finalPath M hE (mainMasks r) s' ∧
      birth M hE (mainMasks r) s = birth M hE (mainMasks r) s' ∧
      assign M hE (mainMasks r) s = assign M hE (mainMasks r) s' := by
  apply preprocessing_congr
  intro e he
  unfold observed
  have hm : e ∈ (hidden M hE).mask r := he
  rw [ite_eq_left hm]

end MatroidProphet.MainAlgorithm

end OAI

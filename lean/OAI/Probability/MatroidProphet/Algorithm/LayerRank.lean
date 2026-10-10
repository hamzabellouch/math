import OAI.Probability.MatroidProphet.Algorithm.Selection
import OAI.Probability.MatroidProphet.Groups
import OAI.Probability.MatroidProphet.PathRankCost

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma mem_nominal_difference_iff (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (e : α) (he : e ∉ M.closure ∅) (b : ℤ) :
    e ∈ nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1) ↔
      nominalBirth M hE κ D C h e = b := by
  simp only [Set.mem_sdiff, mem_nominal_iff_birth_le M hE κ D C h e he]
  omega

lemma lowerCompetition_member (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) {j h : ℕ} (hj : j < h)
    {e : α} (he : e ∈ T j ∩ (nominalPath M hE κ D C j b \
      nominalPath M hE κ D C j (b-1))) :
    e ∈ lowerCompetition M hE κ D C T b h := by
  induction h with
  | zero => omega
  | succ h ih =>
    change e ∈ lowerCompetition M hE κ D C T b h ∪
      (T h ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1)))
    by_cases heq : j = h
    · exact Or.inr (heq ▸ he)
    · exact Or.inl (ih (by omega))

namespace MainAlgorithm
variable {n : ℕ}

lemma candidate_nonloop (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (e : Fin n) (v : Option ℤ)
    (he : candidate M d w e v) : e ∉ M.closure ∅ :=
  fun hx => he.2.2 (M.closure_subset_closure (Set.empty_subset _) hx)

lemma groups_index_of_get (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) {h : ℕ} {i : ℤ} (hi : (groups M d w)[h]? = some i) :
    i ∈ groups M d w ∧ (groups M d w).idxOf i = h := by
  obtain ⟨hh, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact ⟨List.getElem_mem hh, (groups_nodup M d w).idxOf_getElem h hh⟩

noncomputable def groupBirthRegion (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (b : ℤ) : Set (Fin n) :=
  unobservedBirthRegion M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w univ h) (d.H ∪ d.D ∪ d.C : Finset (Fin n)) h b

noncomputable def competition (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (b : ℤ) : Set (Fin n) :=
  lowerCompetition M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w d.T) b h

lemma groupBirthRegion_eligible (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (b : ℤ)
    (hb : b % 2 = (if d.odd then 1 else 0)) {e : Fin n}
    (he : e ∈ groupBirthRegion M hE d w h b ∩ (d.T : Set (Fin n)))
    (hf : e ∉ finalPath M hE d w (b-2)) :
    e ∈ assignedEligible (assign M hE d w) w ∧
      assignedLayer (assign M hE d w) w e = b := by
  classical
  have ht := he.2
  have hr := he.1
  unfold groupBirthRegion unobservedBirthRegion at hr
  split_ifs at hr with ha
  · obtain ⟨⟨⟨_, hc, hg⟩, hX⟩, hO⟩ := hr
    obtain ⟨i, hwi⟩ : ∃ i, w e = some i := Option.ne_none_iff_exists'.mp hc.1
    have hget : (groups M d w)[h]? = some i := hg.symm.trans hwi
    obtain ⟨hi, hidx⟩ := groups_index_of_get M d w hget
    have hbirth : birth M hE d w e i = b := by
      unfold birth
      rw [hidx]
      exact (mem_nominal_difference_iff M hE (2^100) _ _ h e
        (candidate_nonloop M d w e _ hc) b).mp hX
    have hel : eligible M hE d w e i := by
      refine ⟨hO, ?_, hi, ht, ?_, ?_, ?_⟩
      · rwa [← hwi]
      · rwa [hidx, hbirth]
      · rwa [hbirth]
      · rwa [hbirth]
    have has : assign M hE d w e (w e) = some b :=
      (assign_spec M hE d w e _ b).mpr ⟨i, hwi, hel, hbirth⟩
    constructor
    · simp [assignedEligible, has]
    · simp [assignedLayer, has]
  · exact False.elim hr

lemma selection_low_mem_competition (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    (h : ℕ) (b : ℤ) {e : Fin n} (he : e ∈ selection M hE d w π)
    (hb : assignedLayer (assign M hE d w) w e = b)
    (hlow : ¬ ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i) :
    e ∈ competition M hE d w h b := by
  have hel := layerGreedy_subset M _ _ _ _ he
  obtain ⟨i, hwi, hi, hbi⟩ := (assign_spec M hE d w e _ _).mp
    (assigned_some_of_eligible (assign M hE d w) w e hel)
  have hidx : (groups M d w).idxOf i < h := by
    by_contra hn
    exact hlow ⟨i, hwi, by omega⟩
  apply lowerCompetition_member M hE (2^100) _ _ _ b hidx
  constructor
  · exact ⟨hi.2.2.2.1, by simpa only [hwi] using hi.2.1, hwi.trans (groups_get?_idxOf M d w i hi.2.2.1).symm⟩
  · apply (mem_nominal_difference_iff M hE (2^100) _ _ _ e
      (candidate_nonloop M d w e _ hi.2.1) b).mpr
    exact hbi.trans hb

theorem selection_cumulative_rank (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    (h : ℕ) (L : Finset ℤ) (hL : ∀ b ∈ L, b % 2 = (if d.odd then 1 else 0)) :
    (∑ b ∈ L, conditionalRank M
      (groupBirthRegion M hE d w h b ∩ (d.T : Set (Fin n)))
      (finalPath M hE d w (b-2) ∪ competition M hE d w h b)) ≤
      ((selection M hE d w π).filter (fun e =>
        ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i)).card := by
  classical
  exact layerGreedy_sum_rank_lower M hE _ _ _ _ L _ _ _
    (fun b hb e he => groupBirthRegion_eligible M hE d w h b (hL b hb) he.1 he.2)
    (fun b _ e he hb hn => selection_low_mem_competition M hE d w π h b he hb hn)

end MainAlgorithm
end MatroidProphet

end OAI

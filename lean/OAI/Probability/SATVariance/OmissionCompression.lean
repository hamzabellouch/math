import OAI.Probability.SATVariance.SupportProbabilities

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def joinedAssignment {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (x : Assignment k × Assignment u) : Assignment n :=
  fun v => Sum.elim x.1 x.2 (e.symm v)

lemma joinedAssignment_inl {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (x : Assignment k × Assignment u) (j : Fin k) :
    joinedAssignment e x (e (Sum.inl j)) = x.1 j := by simp [joinedAssignment]

lemma joinedAssignment_inr {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (x : Assignment k × Assignment u) (j : Fin u) :
    joinedAssignment e x (e (Sum.inr j)) = x.2 j := by simp [joinedAssignment]

lemma joinedAssignment_surjective {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) :
    Function.Surjective (joinedAssignment e) := by
  intro b
  refine ⟨⟨fun j => b (e (Sum.inl j)), fun j => b (e (Sum.inr j))⟩, ?_⟩
  funext v
  obtain ⟨z,rfl⟩ := e.surjective v
  cases z <;> simp [joinedAssignment]

lemma satisfies_joined_merge {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (p : RootData u k) (x : Assignment k × Assignment u) :
    Satisfies (mergeClause e p.1 p.2) (joinedAssignment e x) ↔ DataSatisfies p x := by
  simpa only [joinedAssignment_inl, joinedAssignment_inr, DataSatisfies] using
    satisfies_merge e p.1 p.2 (joinedAssignment e x)

lemma succAbove_lt_succ_iff {M : ℕ} (i : Fin (M+1)) (l j : Fin M) (hi : i.val ≤ l.val) :
    (i.succAbove j).val < l.val+1 ↔ j.val < l.val := by
  by_cases hj : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    have hji : j.val < i.val := hj
    simp only [Fin.val_castSucc]
    omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hj)]
    simp only [Fin.val_succ, Nat.succ_lt_succ_iff]

abbrev omittedSAT {n k L : ℕ} (i : Fin L) (cs : Fin L → Clause n k) (m : ℕ) : Prop :=
  ∃ a : Assignment n, ∀ j : Fin L, j.val < m → j ≠ i → Satisfies (cs j) a

lemma finiteSAT_omittedSAT {n k L m : ℕ} {i : Fin L} {cs : Fin L → Clause n k}
    (h : finiteSAT cs m) : omittedSAT i cs m := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,fun j hj _ => ha j hj⟩

lemma omittedSAT_before {n k L m : ℕ} {i : Fin L} {cs : Fin L → Clause n k}
    (hm : m ≤ i.val) : omittedSAT i cs m ↔ finiteSAT cs m := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,fun j hj => ha j hj ?_⟩
    intro hji
    subst j
    omega
  · exact finiteSAT_omittedSAT

lemma omittedTime_nonneg_diff {n k L : ℕ} (i : Fin L) (cs : Fin L → Clause n k) :
    0 ≤ omittedTime i cs-finiteTime cs := by
  unfold omittedTime finiteTime
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro m _
  by_cases h : finiteSAT cs m.val
  · simp only [ite_eq_left h, ite_eq_left (finiteSAT_omittedSAT (i := i) h), sub_self, le_refl]
  · simp only [ite_eq_right h, sub_zero]
    split <;> norm_num

lemma omittedSAT_compressed {n k u M : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (i : Fin (M+1)) (c : Clause n k) (ps : Fin M → RootData u k)
    (l : Fin M) (hi : i.val ≤ l.val) :
    omittedSAT i (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) (l.val+1) ↔
      (pairPrefix Finset.univ ps l.val).Nonempty := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨x,rfl⟩ := joinedAssignment_surjective e b
    refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩⟩
    have hh := hb (i.succAbove j) ((succAbove_lt_succ_iff i l j hi).mpr hj) (Fin.succAbove_ne i j)
    simpa only [Fin.insertNth_apply_succAbove, satisfies_joined_merge] using hh
  · rintro ⟨x,hx⟩
    refine ⟨joinedAssignment e x,fun j hj hji => ?_⟩
    obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq hji
    rw [Fin.insertNth_apply_succAbove, satisfies_joined_merge]
    exact (Finset.mem_filter.mp hx).2 t ((succAbove_lt_succ_iff i l t hi).mp hj)

lemma fullSAT_compressed {n k u M : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (i : Fin (M+1)) (c : Clause n k) (ps : Fin M → RootData u k)
    (l : Fin M) (hi : i.val ≤ l.val) :
    finiteSAT (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) (l.val+1) ↔
      ∃ x ∈ pairPrefix Finset.univ ps l.val, Satisfies c (joinedAssignment e x) := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨x,rfl⟩ := joinedAssignment_surjective e b
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩, ?_⟩
    · have hh := hb (i.succAbove j) ((succAbove_lt_succ_iff i l j hi).mpr hj)
      simpa only [Fin.insertNth_apply_succAbove, satisfies_joined_merge] using hh
    · simpa only [Fin.insertNth_apply_same] using hb i (by omega)
  · rintro ⟨x,hx,hc⟩
    refine ⟨joinedAssignment e x,fun j hj => ?_⟩
    by_cases hji : j = i
    · subst j
      simpa only [Fin.insertNth_apply_same] using hc
    · obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq hji
      rw [Fin.insertNth_apply_succAbove, satisfies_joined_merge]
      exact (Finset.mem_filter.mp hx).2 t ((succAbove_lt_succ_iff i l t hi).mp hj)

lemma deletion_difference_le_rewards {n k u M : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (i : Fin (M+1)) (c : Clause n k) (a : Assignment k)
    (hc : ∀ x, ¬Satisfies c (joinedAssignment e x) ↔ x.1 = a)
    (ps : Fin M → RootData u k) :
    omittedTime i (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) -
      finiteTime (i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)) ≤
      dataRewards (forcedReward a) Finset.univ ps := by
  let cs : Fin (M+1) → Clause n k := i.insertNth c (fun j => mergeClause e (ps j).1 (ps j).2)
  change omittedTime i cs-finiteTime cs ≤ _
  unfold omittedTime finiteTime dataRewards
  rw [← Finset.sum_sub_distrib, Fin.sum_univ_succ]
  have hzero : finiteSAT cs 0 := ⟨fun _ => false,fun _ hj => by omega⟩
  change ((if omittedSAT i cs 0 then (1 : ℝ) else 0)-(if finiteSAT cs 0 then 1 else 0)) +
    ∑ l : Fin M, ((if omittedSAT i cs (l.val+1) then 1 else 0)-(if finiteSAT cs (l.val+1) then 1 else 0)) ≤ _
  rw [ite_eq_left hzero, ite_eq_left (finiteSAT_omittedSAT (i := i) hzero), sub_self, zero_add]
  apply Finset.sum_le_sum
  intro l _
  change (if omittedSAT i cs (l.val+1) then (1 : ℝ) else 0) -
    (if finiteSAT cs (l.val+1) then 1 else 0) ≤ forcedReward a (pairPrefix Finset.univ ps l.val)
  by_cases hi : i.val ≤ l.val
  · by_cases hs : finiteSAT cs (l.val+1)
    · simp only [ite_eq_left hs, ite_eq_left (finiteSAT_omittedSAT (i := i) hs), sub_self]
      exact forcedReward_nonneg _ _
    by_cases ho : omittedSAT i cs (l.val+1)
    · have hp := (omittedSAT_compressed e i c ps l hi).mp ho
      have hf : ∀ x ∈ pairPrefix Finset.univ ps l.val, x.1 = a := by
        intro x hx
        apply (hc x).mp
        intro hsat
        exact hs ((fullSAT_compressed e i c ps l hi).mpr ⟨x,hx,hsat⟩)
      have hforce : (pairPrefix Finset.univ ps l.val).Nonempty ∧
          ∀ x ∈ pairPrefix Finset.univ ps l.val, x.1 = a := ⟨hp,hf⟩
      simp only [ite_eq_left ho, ite_eq_right hs, sub_zero, forcedReward, ite_eq_left hforce, le_refl]
    · simp only [ite_eq_right hs, ite_eq_right ho, sub_self]
      exact forcedReward_nonneg _ _
  · have he := omittedSAT_before (cs := cs) (i := i) (by omega : l.val+1 ≤ i.val)
    by_cases hs : finiteSAT cs (l.val+1)
    · simp only [ite_eq_left hs, ite_eq_left (he.mpr hs), sub_self]
      exact forcedReward_nonneg _ _
    · have ho : ¬omittedSAT i cs (l.val+1) := fun h => hs (he.mp h)
      simp only [ite_eq_right hs, ite_eq_right ho, sub_self]
      exact forcedReward_nonneg _ _

lemma clause_root_presentation {n k : ℕ} (c : Clause n k) :
    ∃ (e : Fin k ⊕ Fin (n-k) ≃ Fin n) (a : Assignment k),
      ∀ x, ¬Satisfies c (joinedAssignment e x) ↔ x.1 = a := by
  unfold Clause at c
  let R : Set (Fin n) := ↑c.1.1
  have hR : Fintype.card R = k := by
    exact (Fintype.card_of_subtype c.1.1 (fun _ => Iff.rfl)).trans c.1.property
  have hRc : Fintype.card (↥Rᶜ) = n-k := by
    rw [Fintype.card_compl_set, Fintype.card_fin, hR]
  let er : Fin k ≃ R := (Fintype.equivFinOfCardEq hR).symm
  let eu : Fin (n-k) ≃ ↥Rᶜ := (Fintype.equivFinOfCardEq hRc).symm
  let e : Fin k ⊕ Fin (n-k) ≃ Fin n :=
    (Equiv.sumCongr er eu).trans (Equiv.Set.sumCompl R)
  let a : Assignment k := fun j => !(c.2 (er j))
  refine ⟨e,a,fun x => ?_⟩
  have hinl (j : Fin k) : e (Sum.inl j) = (er j).val := rfl
  have hs : Satisfies c (joinedAssignment e x) ↔ ∃ j, x.1 j = c.2 (er j) := by
    constructor
    · rintro ⟨v,hv⟩
      obtain ⟨j,rfl⟩ := er.surjective v
      exact ⟨j, by simpa only [← hinl, joinedAssignment_inl] using hv⟩
    · rintro ⟨j,hj⟩
      exact ⟨er j, by simpa only [← hinl, joinedAssignment_inl] using hj⟩
  rw [hs, not_exists]
  constructor
  · intro h
    exact funext fun j => Bool.eq_not_iff.mpr (h j)
  · intro h j
    exact Bool.eq_not_iff.mp (congrFun h j)

lemma favg_insertNth.{u_1} {α : Type u_1} [Fintype α] {M : ℕ} (i : Fin (M+1))
    (f : (Fin (M+1) → α) → ℝ) :
    favg f = favg (fun c : α => favg (fun w : Fin M → α => f (i.insertNth c w))) := by
  rw [← favg_equiv (Fin.insertNthEquiv (fun _ => α) i) f, favg_prod]
  rfl

end RandomKSAT

end

end OAI

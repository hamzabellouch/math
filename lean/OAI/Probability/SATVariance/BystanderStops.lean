import OAI.Probability.SATVariance.ShuffleAverages

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def listSAT {n k : ℕ} (l : List (Clause n k)) : Prop :=
  ∃ a : Assignment n, ∀ c ∈ l, Satisfies c a

lemma listSAT_nil (n k : ℕ) : listSAT ([] : List (Clause n k)) :=
  ⟨fun _ => false, by simp⟩

lemma listSAT_sublist {n k : ℕ} {l r : List (Clause n k)} (h : l.Sublist r)
    (hr : listSAT r) : listSAT l := by
  obtain ⟨a,ha⟩ := hr
  exact ⟨a,fun c hc => ha c (h.subset hc)⟩

lemma listSAT_perm {n k : ℕ} {l r : List (Clause n k)} (h : l.Perm r) :
    listSAT l ↔ listSAT r := by
  constructor <;> rintro ⟨a,ha⟩ <;> refine ⟨a,fun c hc => ?_⟩
  · exact ha c (h.mem_iff.mpr hc)
  · exact ha c (h.mem_iff.mp hc)

def listStop {n k : ℕ} (l : List (Clause n k)) : ℕ :=
  Nat.find (show ∃ m : ℕ, m = l.length+1 ∨ ¬listSAT (l.take m) from ⟨_,Or.inl rfl⟩)

lemma listStop_le {n k : ℕ} (l : List (Clause n k)) : listStop l ≤ l.length+1 :=
  Nat.find_min' _ (Or.inl rfl)

lemma lt_listStop_iff {n k m : ℕ} (l : List (Clause n k)) :
    m < listStop l ↔ m ≤ l.length ∧ listSAT (l.take m) := by
  constructor
  · intro hm
    refine ⟨by have := listStop_le l; omega, ?_⟩
    have hh := Nat.find_min (show ∃ j : ℕ, j = l.length+1 ∨ ¬listSAT (l.take j)
      from ⟨_,Or.inl rfl⟩) hm
    exact not_not.mp (fun h => hh (Or.inr h))
  · rintro ⟨hm,hs⟩
    apply (Nat.lt_find_iff _ _).mpr
    intro j hj
    rintro (he | hn)
    · omega
    · apply hn
      exact listSAT_sublist (List.take_sublist_take_left hj) hs

lemma listStop_pos {n k : ℕ} (l : List (Clause n k)) : 0 < listStop l := by
  rw [lt_listStop_iff]
  exact ⟨Nat.zero_le _,by simpa using listSAT_nil n k⟩

def Harmless {n k : ℕ} (c : Clause n k) (l : List (Clause n k)) : Prop :=
  ∀ r, r.Sublist l → (listSAT (c::r) ↔ listSAT r)

lemma harmless_private {n k : ℕ} (c : Clause n k) (l : List (Clause n k))
    (v : c.1.1) (hv : ∀ d ∈ l, v.val ∉ d.1.1) : Harmless c l := by
  intro r hr
  constructor
  · exact listSAT_sublist (List.sublist_cons_self _ _)
  · rintro ⟨a,ha⟩
    refine ⟨Function.update a v.val (c.2 v), ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with he | hd
    · subst d
      exact ⟨v,by simp⟩
    · obtain ⟨w,hw⟩ := ha d hd
      refine ⟨w,?_⟩
      have hne : w.val ≠ v.val := by
        intro he
        apply hv d (hr.subset hd)
        exact he ▸ w.property
      simpa only [Function.update_of_ne hne] using hw

lemma take_insertIdx_perm.{u_1} {α : Type u_1} (l : List α) (c : α) (i m : ℕ)
    (hi : i ≤ l.length) (him : i < m) :
    ((l.insertIdx i c).take m).Perm (c::l.take (m-1)) := by
  induction l generalizing i m with
  | nil =>
    have : i = 0 := by simpa using hi
    subst i
    cases m with
    | zero => omega
    | succ m => simp
  | cons a l ih =>
    cases i with
    | zero =>
      cases m with
      | zero => omega
      | succ m => simp
    | succ i =>
      cases m with
      | zero => omega
      | succ m =>
        have hi' : i ≤ l.length := by simpa using hi
        have him' : i < m := by omega
        have hh := (ih i m hi' him').cons a
        have hm : 0 < m := by omega
        cases m with
        | zero => omega
        | succ m =>
          simpa only [List.insertIdx_succ_cons, List.take_succ_cons, Nat.add_sub_cancel,
            Nat.succ_sub_one] using hh.trans (List.Perm.swap c a _)

lemma listSAT_insert_take {n k : ℕ} (c : Clause n k) (l : List (Clause n k))
    (hc : Harmless c l) (i m : ℕ) (hi : i ≤ l.length) :
    listSAT ((l.insertIdx i c).take m) ↔
      listSAT (l.take (m - if i < m then 1 else 0)) := by
  by_cases him : i < m
  · rw [ite_eq_left him, listSAT_perm (take_insertIdx_perm l c i m hi him)]
    exact hc _ (List.take_sublist _ _)
  · rw [ite_eq_right him, Nat.sub_zero, List.take_insertIdx_eq_take_of_le _ _ m i (by omega)]

lemma listStop_insert {n k : ℕ} (c : Clause n k) (l : List (Clause n k))
    (hc : Harmless c l) (i : ℕ) (hi : i ≤ l.length) :
    listStop (l.insertIdx i c) = listStop l + if i < listStop l then 1 else 0 := by
  apply eq_of_forall_lt_iff
  intro m
  have hl : (l.insertIdx i c).length = l.length+1 := List.length_insertIdx_of_le_length hi c
  rw [lt_listStop_iff, hl, listSAT_insert_take c l hc i m hi]
  have ht := listStop_le l
  by_cases hm : m ≤ l.length+1
  · simp only [hm, true_and]
    have hr : m - (if i < m then 1 else 0) ≤ l.length := by split_ifs <;> omega
    have he := lt_listStop_iff (m := m - (if i < m then 1 else 0)) l
    rw [and_iff_right hr] at he
    rw [← he]
    split_ifs <;> omega
  · simp only [hm, false_and]
    constructor
    · exact False.elim
    · intro h
      have hb : listStop l + (if i < listStop l then 1 else 0) ≤ l.length+2 := by
        have hx : (if i < listStop l then 1 else 0) ≤ (1 : ℕ) := by split_ifs <;> omega
        omega
      omega

end RandomKSAT

end

end OAI

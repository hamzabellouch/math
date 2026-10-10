import OAI.Probability.FreeIsing.Estimates.ColorAutomorphisms

namespace OAI

namespace Problem367

def prefixColorList {d : ℕ} (stem : List (Fin d)) (p : Equiv.Perm (Fin d))
    (w : List (Fin d)) : List (Fin d) :=
  match stem, w with
  | [], w => w.map p
  | _ :: _, [] => []
  | a :: r, b :: w => if a = b then b :: prefixColorList r p w else b :: w

@[simp] lemma prefixColorList_nil {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) : prefixColorList stem p [] = [] := by
  cases stem <;> rfl

@[simp] lemma prefixColorList_head {d : ℕ} (a : Fin d) (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) :
    (prefixColorList (a :: stem) p w).head? = w.head? := by
  cases w with
  | nil => rfl
  | cons b w => by_cases h : a = b <;> simp [prefixColorList, h]

lemma prefixColorList_inverse {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) :
    prefixColorList stem p.symm (prefixColorList stem p w) = w := by
  induction stem generalizing w with
  | nil => simp [prefixColorList, List.map_map, Function.comp_def]
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w => by_cases h : a = b <;> simp [prefixColorList, h, ih]

lemma prefixColorList_append {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) (c : Fin d) :
    ∃ e, prefixColorList stem p (w ++ [c]) = prefixColorList stem p w ++ [e] := by
  induction stem generalizing w with
  | nil => exact ⟨p c, by simp [prefixColorList]⟩
  | cons a r ih =>
    cases w with
    | nil =>
      refine ⟨c, ?_⟩
      by_cases h : a = c <;> simp [prefixColorList, h]
    | cons b w =>
      by_cases h : a = b
      · obtain ⟨e, he⟩ := ih w
        exact ⟨e, by simpa [prefixColorList, h] using congrArg (List.cons b) he⟩
      · exact ⟨c, by simp [prefixColorList, h]⟩

lemma prefixColorList_chain {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (w : List (Fin d)) (hw : w.IsChain (· ≠ ·)) :
    (prefixColorList stem p w).IsChain (· ≠ ·) := by
  induction stem generalizing w with
  | nil =>
    rw [prefixColorList, List.isChain_map]
    exact hw.imp (fun _ _ hab heq => hab (p.injective heq))
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w =>
      by_cases hab : a = b
      · subst a
        cases r with
        | nil =>
          have hpb : p b = b := hp b (by simp)
          have hmap : ((b :: w).map p).IsChain (· ≠ ·) := by
            rw [List.isChain_map]
            exact hw.imp (fun _ _ hne heq => hne (p.injective heq))
          simpa [prefixColorList, hpb] using hmap
        | cons c r =>
          have hp' : ∀ x ∈ (c :: r).getLast?, p x = x := by
            simpa only [List.getLast?_cons_cons] using hp
          have ht := ih hp' w hw.tail
          simp only [prefixColorList]
          apply List.isChain_cons.mpr
          refine ⟨?_, ht⟩
          intro y hy
          rw [prefixColorList_head] at hy
          exact hw.rel_head? hy
      · simpa [prefixColorList, hab] using hw

@[simp] lemma prefixColorList_length {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) :
    (prefixColorList stem p w).length = w.length := by
  induction stem generalizing w with
  | nil => simp [prefixColorList]
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w => by_cases h : a = b <;> simp [prefixColorList, h, ih]

lemma prefixColorList_on_subtree {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) :
    prefixColorList stem p (stem ++ w) = stem ++ w.map p := by
  induction stem with
  | nil => rfl
  | cons a r ih => simp [prefixColorList, ih]

lemma prefixColorList_eq_of_length_le {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) (hw : w.length ≤ stem.length) :
    prefixColorList stem p w = w := by
  induction stem generalizing w with
  | nil =>
    have hw' : w = [] := List.length_eq_zero_iff.mp (by simpa using hw)
    simp [hw']
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w =>
      have hw' : w.length ≤ r.length := by simpa using hw
      by_cases h : a = b <;> simp [prefixColorList, h, ih w hw']

lemma prefixColorList_eq_of_not_prefix {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) (hw : ¬ stem <+: w) :
    prefixColorList stem p w = w := by
  induction stem generalizing w with
  | nil => exact (hw List.nil_prefix).elim
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w =>
      by_cases hab : a = b
      · have htail : ¬ r <+: w := by
          intro hr
          exact hw (List.cons_prefix_cons.mpr ⟨hab, hr⟩)
        simp [prefixColorList, hab, ih w htail]
      · simp [prefixColorList, hab]

lemma prefixColor_inverse_fixes {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c) :
    ∀ c ∈ stem.getLast?, p.symm c = c := by
  intro c hc
  apply p.injective
  simp [hp c hc]

def prefixColorMap {d : ℕ} (stem : List (Fin d)) (p : Equiv.Perm (Fin d))
    (hp : ∀ c ∈ stem.getLast?, p c = c) (u : TreeVertex d) : TreeVertex d :=
  ⟨prefixColorList stem p u.1, prefixColorList_chain stem p hp u.1 u.2⟩

@[simp] lemma prefixColorMap_symm_apply {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) :
    prefixColorMap stem p.symm (prefixColor_inverse_fixes stem p hp)
      (prefixColorMap stem p hp u) = u := by
  apply Subtype.ext
  exact prefixColorList_inverse stem p u.1

lemma prefixColorMap_adj {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    {u v : TreeVertex d} (h : treeAdj u v) :
    treeAdj (prefixColorMap stem p hp u) (prefixColorMap stem p hp v) := by
  change (∃ a, prefixColorList stem p v.1 = prefixColorList stem p u.1 ++ [a]) ∨
    (∃ a, prefixColorList stem p u.1 = prefixColorList stem p v.1 ++ [a])
  rcases h with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [ha]
    exact Or.inl (prefixColorList_append stem p u.1 a)
  · rw [ha]
    exact Or.inr (prefixColorList_append stem p v.1 a)

def prefixColorAut {d : ℕ} (stem : List (Fin d)) (p : Equiv.Perm (Fin d))
    (hp : ∀ c ∈ stem.getLast?, p c = c) : TreeAut d where
  toEquiv :=
    { toFun := prefixColorMap stem p hp
      invFun := prefixColorMap stem p.symm (prefixColor_inverse_fixes stem p hp)
      left_inv := prefixColorMap_symm_apply stem p hp
      right_inv := by
        intro u
        apply Subtype.ext
        simpa only [prefixColorMap, Equiv.symm_symm] using
          prefixColorList_inverse stem p.symm u.1 }
  map_adj := by
    intro u v
    change treeAdj (prefixColorMap stem p hp u) (prefixColorMap stem p hp v) ↔ treeAdj u v
    constructor
    · intro h
      simpa using prefixColorMap_adj stem p.symm (prefixColor_inverse_fixes stem p hp) h
    · exact prefixColorMap_adj stem p hp

@[simp] theorem prefixColorAut_val {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) :
    ((prefixColorAut stem p hp).toEquiv u).1 = prefixColorList stem p u.1 := rfl

@[simp] theorem prefixColorAut_length {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) : ((prefixColorAut stem p hp).toEquiv u).1.length = u.1.length := by
  simp

theorem prefixColorAut_fixes_ball {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) (hu : u.1.length ≤ stem.length) :
    (prefixColorAut stem p hp).toEquiv u = u := by
  apply Subtype.ext
  exact prefixColorList_eq_of_length_le stem p u.1 hu

theorem prefixColorAut_fixes_complement {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) (hu : ¬ stem <+: u.1) :
    (prefixColorAut stem p hp).toEquiv u = u := by
  apply Subtype.ext
  exact prefixColorList_eq_of_not_prefix stem p u.1 hu

end Problem367

end OAI

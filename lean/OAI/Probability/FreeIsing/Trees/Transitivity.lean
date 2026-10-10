import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

namespace Problem367

namespace TreeAut

def refl (d : ℕ) : TreeAut d where
  toEquiv := Equiv.refl _
  map_adj := fun _ _ => Iff.rfl

def symm {d : ℕ} (g : TreeAut d) : TreeAut d where
  toEquiv := g.toEquiv.symm
  map_adj := by
    intro u v
    simpa only [Equiv.apply_symm_apply] using
      (g.map_adj (g.toEquiv.symm u) (g.toEquiv.symm v)).symm

def trans {d : ℕ} (g h : TreeAut d) : TreeAut d where
  toEquiv := g.toEquiv.trans h.toEquiv
  map_adj := by
    intro u v
    exact (h.map_adj (g.toEquiv u) (g.toEquiv v)).trans (g.map_adj u v)

end TreeAut

def prefixFlipWord {α : Type*} [DecidableEq α] (c : α) : List α → List α
  | [] => [c]
  | a :: w => if c = a then w else c :: a :: w

theorem prefixFlipWord_chain {α : Type*} [DecidableEq α] (c : α)
    (w : List α) (hw : w.IsChain (· ≠ ·)) :
    (prefixFlipWord c w).IsChain (· ≠ ·) := by
  cases w with
  | nil => simp [prefixFlipWord]
  | cons a w =>
    by_cases h : c = a
    · simp only [prefixFlipWord, ite_eq_left h]
      exact hw.tail
    · simp only [prefixFlipWord, ite_eq_right h, List.isChain_cons_cons]
      exact ⟨h, hw⟩

theorem prefixFlipWord_involutive {α : Type*} [DecidableEq α] (c : α)
    (w : List α) (hw : w.IsChain (· ≠ ·)) :
    prefixFlipWord c (prefixFlipWord c w) = w := by
  cases w with
  | nil => simp [prefixFlipWord]
  | cons a w =>
    by_cases h : c = a
    · subst a
      cases w with
      | nil => simp [prefixFlipWord]
      | cons b w =>
        have hcb : c ≠ b := (List.isChain_cons_cons.mp hw).1
        simp [prefixFlipWord, hcb]
    · simp [prefixFlipWord, h]

def prefixFlip {d : ℕ} (c : Fin d) (w : TreeVertex d) : TreeVertex d :=
  ⟨prefixFlipWord c w.1, prefixFlipWord_chain c w.1 w.2⟩

@[simp] theorem prefixFlip_twice {d : ℕ} (c : Fin d) (w : TreeVertex d) :
    prefixFlip c (prefixFlip c w) = w := by
  apply Subtype.ext
  exact prefixFlipWord_involutive c w.1 w.2

theorem prefixFlipWord_append_adj {α : Type*} [DecidableEq α]
    (c a : α) (w : List α) :
    (∃ b, prefixFlipWord c (w ++ [a]) = prefixFlipWord c w ++ [b]) ∨
    (∃ b, prefixFlipWord c w = prefixFlipWord c (w ++ [a]) ++ [b]) := by
  cases w with
  | nil =>
    by_cases h : c = a
    · subst a
      right
      exact ⟨c, by simp [prefixFlipWord]⟩
    · left
      exact ⟨a, by simp [prefixFlipWord, h]⟩
  | cons b w =>
    left
    refine ⟨a, ?_⟩
    by_cases h : c = b <;> simp [prefixFlipWord, h]

theorem prefixFlip_adj {d : ℕ} (c : Fin d) {u v : TreeVertex d}
    (h : treeAdj u v) : treeAdj (prefixFlip c u) (prefixFlip c v) := by
  rcases h with ⟨a, h⟩ | ⟨a, h⟩
  · simpa only [treeAdj, prefixFlip, h] using prefixFlipWord_append_adj c a u.1
  · simpa only [treeAdj, prefixFlip, h, or_comm] using prefixFlipWord_append_adj c a v.1

def prefixTreeAut {d : ℕ} (c : Fin d) : TreeAut d where
  toEquiv :=
    { toFun := prefixFlip c
      invFun := prefixFlip c
      left_inv := prefixFlip_twice c
      right_inv := prefixFlip_twice c }
  map_adj := by
    intro u v
    constructor
    · intro h
      change treeAdj (prefixFlip c u) (prefixFlip c v) at h
      have h' := prefixFlip_adj c h
      simpa only [prefixFlip_twice] using h'
    · exact prefixFlip_adj c

theorem exists_treeAut_to_root {d : ℕ} (u : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = ⟨[], List.IsChain.nil⟩ := by
  rcases u with ⟨w, hw⟩
  induction w with
  | nil => exact ⟨TreeAut.refl d, rfl⟩
  | cons a w ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.tail
    obtain ⟨g, hg⟩ := ih hw'
    refine ⟨(prefixTreeAut a).trans g, ?_⟩
    change g.toEquiv (prefixFlip a ⟨a :: w, hw⟩) = _
    have hflip : prefixFlip a ⟨a :: w, hw⟩ = ⟨w, hw'⟩ := by
      apply Subtype.ext
      simp [prefixFlip, prefixFlipWord]
    rw [hflip]
    exact hg

theorem exists_treeAut_map {d : ℕ} (u v : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = v := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root u
  obtain ⟨h, hh⟩ := exists_treeAut_to_root v
  refine ⟨g.trans h.symm, ?_⟩
  change h.toEquiv.symm (g.toEquiv u) = v
  rw [hg, ← hh]
  exact h.toEquiv.symm_apply_apply v

theorem treeAut_transitive {d : ℕ} (u v : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = v :=
  exists_treeAut_map u v

theorem exists_treeAut_swap_of_adj {d : ℕ} {u v : TreeVertex d}
    (huv : treeAdj u v) :
    ∃ g : TreeAut d, g.toEquiv u = v ∧ g.toEquiv v = u := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root u
  have hgv : treeAdj (⟨[], List.IsChain.nil⟩ : TreeVertex d) (g.toEquiv v) := by
    rw [← hg]
    exact (g.map_adj u v).2 huv
  obtain ⟨c, hc⟩ : ∃ c : Fin d, (g.toEquiv v).1 = [c] := by
    rcases hgv with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, by simpa using hc⟩
    · have := congrArg List.length hc
      simp at this
  have hgv' : g.toEquiv v = ⟨[c], List.IsChain.singleton c⟩ := Subtype.ext hc
  refine ⟨(g.trans (prefixTreeAut c)).trans g.symm, ?_, ?_⟩
  · change g.toEquiv.symm (prefixFlip c (g.toEquiv u)) = v
    rw [hg]
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hgv']
    apply Subtype.ext
    rfl
  · change g.toEquiv.symm (prefixFlip c (g.toEquiv v)) = u
    rw [hgv']
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hg]
    apply Subtype.ext
    simp [prefixFlip, prefixFlipWord]

end Problem367

end

end OAI

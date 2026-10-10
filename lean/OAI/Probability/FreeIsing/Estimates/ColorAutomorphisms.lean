import OAI.Probability.FreeIsing.Model

namespace OAI

namespace Problem367

def colorPermMap {d : ℕ} (p : Equiv.Perm (Fin d)) (u : TreeVertex d) : TreeVertex d :=
  ⟨u.1.map p, by
    change (u.1.map p).IsChain (· ≠ ·)
    rw [List.isChain_map]
    exact u.2.imp (fun _ _ hab hab' => hab (p.injective hab'))⟩

@[simp] theorem colorPermMap_val {d : ℕ} (p : Equiv.Perm (Fin d))
    (u : TreeVertex d) : (colorPermMap p u).1 = u.1.map p := rfl

@[simp] theorem colorPermMap_symm_apply {d : ℕ} (p : Equiv.Perm (Fin d))
    (u : TreeVertex d) : colorPermMap p.symm (colorPermMap p u) = u := by
  apply Subtype.ext
  simp [colorPermMap, List.map_map, Function.comp_def]

theorem colorPermMap_adj {d : ℕ} (p : Equiv.Perm (Fin d)) {u v : TreeVertex d}
    (h : treeAdj u v) : treeAdj (colorPermMap p u) (colorPermMap p v) := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl ⟨p c, by simp [colorPermMap, hc]⟩
  · exact Or.inr ⟨p c, by simp [colorPermMap, hc]⟩

def colorPermAut {d : ℕ} (p : Equiv.Perm (Fin d)) : TreeAut d where
  toEquiv :=
    { toFun := colorPermMap p
      invFun := colorPermMap p.symm
      left_inv := colorPermMap_symm_apply p
      right_inv := by
        intro u
        simpa only [Equiv.symm_symm] using colorPermMap_symm_apply p.symm u }
  map_adj := by
    intro u v
    change treeAdj (colorPermMap p u) (colorPermMap p v) ↔ treeAdj u v
    constructor
    · intro h
      simpa using colorPermMap_adj p.symm h
    · exact colorPermMap_adj p

@[simp] theorem colorPermAut_val {d : ℕ} (p : Equiv.Perm (Fin d))
    (u : TreeVertex d) : ((colorPermAut p).toEquiv u).1 = u.1.map p := rfl

@[simp] theorem colorPermAut_length {d : ℕ} (p : Equiv.Perm (Fin d))
    (u : TreeVertex d) : ((colorPermAut p).toEquiv u).1.length = u.1.length := by
  simp

@[simp] theorem colorPermAut_nil {d : ℕ} (p : Equiv.Perm (Fin d))
    (h : List.IsChain (fun a b : Fin d => a ≠ b) []) :
    (colorPermAut p).toEquiv ⟨[], h⟩ = ⟨[], h⟩ := by
  apply Subtype.ext
  rfl

def branchColorList {d : ℕ} (p : Fin d → Equiv.Perm (Fin d)) :
    List (Fin d) → List (Fin d)
  | [] => []
  | c :: w => c :: w.map (p c)

lemma branchColorList_chain {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (w : List (Fin d)) (hw : w.IsChain (· ≠ ·)) :
    (branchColorList p w).IsChain (· ≠ ·) := by
  cases w with
  | nil => simp [branchColorList]
  | cons c w =>
    have h := (colorPermMap (p c) ⟨c :: w, hw⟩).2
    change ((c :: w).map (p c)).IsChain (· ≠ ·) at h
    simpa [colorPermMap, branchColorList, hp c] using h

lemma branchColorList_inverse {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (w : List (Fin d)) :
    branchColorList (fun c => (p c).symm) (branchColorList p w) = w := by
  cases w <;> simp [branchColorList, List.map_map, Function.comp_def]

lemma branchColorList_append {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (w : List (Fin d)) (a : Fin d) :
    ∃ b, branchColorList p (w ++ [a]) = branchColorList p w ++ [b] := by
  cases w with
  | nil => exact ⟨a, rfl⟩
  | cons c w => exact ⟨p c a, by simp [branchColorList]⟩

def branchColorMap {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (u : TreeVertex d) : TreeVertex d :=
  ⟨branchColorList p u.1, branchColorList_chain p hp u.1 u.2⟩

lemma branchColorMap_adj {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) {u v : TreeVertex d} (h : treeAdj u v) :
    treeAdj (branchColorMap p hp u) (branchColorMap p hp v) := by
  change (∃ a, branchColorList p v.1 = branchColorList p u.1 ++ [a]) ∨
    (∃ a, branchColorList p u.1 = branchColorList p v.1 ++ [a])
  rcases h with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [ha]
    exact Or.inl (branchColorList_append p u.1 a)
  · rw [ha]
    exact Or.inr (branchColorList_append p v.1 a)

lemma branchColor_inverse_fixes {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (c : Fin d) : (p c).symm c = c := by
  apply (p c).injective
  simp [hp c]

@[simp] lemma branchColorMap_symm_apply {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (u : TreeVertex d) :
    branchColorMap (fun c => (p c).symm) (branchColor_inverse_fixes p hp)
      (branchColorMap p hp u) = u := by
  apply Subtype.ext
  exact branchColorList_inverse p u.1

def branchColorAut {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) : TreeAut d where
  toEquiv :=
    { toFun := branchColorMap p hp
      invFun := branchColorMap (fun c => (p c).symm) (branchColor_inverse_fixes p hp)
      left_inv := branchColorMap_symm_apply p hp
      right_inv := by
        intro u
        apply Subtype.ext
        simpa only [branchColorMap, Equiv.symm_symm] using
          branchColorList_inverse (fun c => (p c).symm) u.1 }
  map_adj := by
    intro u v
    change treeAdj (branchColorMap p hp u) (branchColorMap p hp v) ↔ treeAdj u v
    constructor
    · intro h
      simpa using branchColorMap_adj (fun c => (p c).symm)
        (branchColor_inverse_fixes p hp) h
    · exact branchColorMap_adj p hp

@[simp] theorem branchColorAut_val {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (u : TreeVertex d) :
    ((branchColorAut p hp).toEquiv u).1 = branchColorList p u.1 := rfl

@[simp] theorem branchColorAut_length {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (u : TreeVertex d) :
    ((branchColorAut p hp).toEquiv u).1.length = u.1.length := by
  rcases u with ⟨w, hw⟩
  cases w <;> simp [branchColorList]

@[simp] theorem branchColorAut_singleton {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (c : Fin d)
    (h : List.IsChain (fun a b : Fin d => a ≠ b) [c]) :
    (branchColorAut p hp).toEquiv ⟨[c], h⟩ = ⟨[c], h⟩ := by
  apply Subtype.ext
  rfl

end Problem367

end OAI

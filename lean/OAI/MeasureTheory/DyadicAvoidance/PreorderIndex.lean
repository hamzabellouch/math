import OAI.MeasureTheory.DyadicAvoidance.TreePreorder
import OAI.MeasureTheory.DyadicAvoidance.TreePreorderRank

namespace OAI

universe u_α u_β

namespace Problem310.PreorderIndex

private theorem idxOf_map_injective {α : Type u_α} {β : Type u_β} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (a : α) (l : List α) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  classical
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : b = a
    · subst b
      simp
    · have hfba : f b ≠ f a := fun he => h (hf he)
      simp only [List.map_cons, List.idxOf_cons_ne _ hfba, List.idxOf_cons_ne _ h, ih]

private theorem idxOf_flatMap_uniform {α : Type u_α} {β : Type u_β} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (l : List α) (f : α → List β) (R : ℕ) (hlen : ∀ a, (f a).length = R)
    (a : α) (b : β) (ha : a ∈ l) (hb : b ∈ f a)
    (hdisjoint : ∀ c, c ≠ a → b ∉ f c) :
    (l.flatMap f).idxOf b = l.idxOf a * R + (f a).idxOf b := by
  classical
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    by_cases hca : c = a
    · subst c
      rw [List.flatMap_cons, List.idxOf_append_of_mem hb]
      simp
    · have ha' : a ∈ l := by simpa [Ne.symm hca] using ha
      rw [List.flatMap_cons, List.idxOf_append_of_notMem (hdisjoint c hca),
        hlen c, ih ha', List.idxOf_cons_ne _ hca]
      simp only [Nat.succ_eq_add_one]
      ring

theorem size_eq_one_add_edgeCount (K d : ℕ) :
    TreePreorderRank.size K d = 1 + TreePreorder.edgeCount K d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [TreePreorderRank.size, TreePreorder.edgeCount, ih]

/-- The arithmetic preorder rank agrees with the actual list enumeration.
The root is omitted from `edgePaths`, hence the offset by one. -/
theorem rank_eq_idxOf_add_one {K d : ℕ} {p : List (Fin K)}
    (hp : p ∈ TreePreorder.edgePaths K d) :
    TreePreorderRank.rank d p = (TreePreorder.edgePaths K d).idxOf p + 1 := by
  induction d generalizing p with
  | zero => simp at hp
  | succ d ih =>
    cases p with
    | nil => simp [TreePreorder.mem_edgePaths_iff] at hp
    | cons i p =>
      have hplen : p.length ≤ d := by
        have h := (TreePreorder.mem_edgePaths_iff K (d + 1) (i :: p)).mp hp
        simpa using h.2
      let block : Fin K → List (List (Fin K)) := fun j =>
        [j] :: (TreePreorder.edgePaths K d).map (List.cons j)
      have hlen (j : Fin K) : (block j).length = 1 + TreePreorder.edgeCount K d := by
        simp [block, Nat.add_comm]
      have hmem : i :: p ∈ block i := by
        by_cases hp0 : p = []
        · subst p
          simp [block]
        · apply List.mem_cons.mpr
          right
          apply List.mem_map.mpr
          exact ⟨p, (TreePreorder.mem_edgePaths_iff K d p).mpr ⟨hp0, hplen⟩, rfl⟩
      have hdisjoint (j : Fin K) (hji : j ≠ i) : i :: p ∉ block j := by
        intro hm
        obtain ⟨s, he⟩ := TreePreorder.mem_childBlock_prefix K d j (i :: p) hm
        exact hji (List.cons.inj he).1.symm
      have hindex := idxOf_flatMap_uniform (List.finRange K) block
        (1 + TreePreorder.edgeCount K d) hlen i (i :: p)
        (List.mem_finRange i) hmem hdisjoint
      simp only [List.idxOf_finRange] at hindex
      change (TreePreorder.edgePaths K (d + 1)).idxOf (i :: p) =
        i.val * (1 + TreePreorder.edgeCount K d) + (block i).idxOf (i :: p) at hindex
      rw [TreePreorderRank.rank_cons, hindex, size_eq_one_add_edgeCount]
      by_cases hp0 : p = []
      · subst p
        simp [block]
        omega
      · have hpedge := (TreePreorder.mem_edgePaths_iff K d p).mpr ⟨hp0, hplen⟩
        have hneq : [i] ≠ i :: p := by
          intro h
          exact hp0 (List.cons.inj h).2.symm
        have hbi : (block i).idxOf (i :: p) =
            (TreePreorder.edgePaths K d).idxOf p + 1 := by
          dsimp only [block]
          rw [List.idxOf_cons_ne _ hneq, idxOf_map_injective (List.cons i)
            (by intro a b h; exact (List.cons.inj h).2)]
        rw [hbi, ih hpedge]
        omega

theorem edgeRank_eq_idxOf {K d : ℕ} {p : List (Fin K)}
    (hp : p ∈ TreePreorder.edgePaths K d) :
    TreePreorderRank.edgeRank d p = (TreePreorder.edgePaths K d).idxOf p := by
  rw [TreePreorderRank.edgeRank, rank_eq_idxOf_add_one hp]
  omega

end Problem310.PreorderIndex

end OAI

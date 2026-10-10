import OAI.Probability.FreeIsing.Trees.PathSideBranches
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

theorem map_reachable_avoiding {d : ℕ} (g : TreeAut d)
    {p a b : TreeVertex d}
    (h : Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ p ∧ y ≠ p ∧ treeAdj x y) a b) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ g.toEquiv p ∧
        y ≠ g.toEquiv p ∧ treeAdj x y) (g.toEquiv a) (g.toEquiv b) := by
  induction h with
  | refl => exact .refl
  | tail h hxy ih =>
      exact ih.tail ⟨fun he => hxy.1 (g.toEquiv.injective he),
        fun he => hxy.2.1 (g.toEquiv.injective he), (g.map_adj _ _).mpr hxy.2.2⟩

theorem map_reachable_avoiding_iff {d : ℕ} (g : TreeAut d)
    (p a b : TreeVertex d) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ g.toEquiv p ∧
        y ≠ g.toEquiv p ∧ treeAdj x y) (g.toEquiv a) (g.toEquiv b) ↔
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ p ∧ y ≠ p ∧ treeAdj x y) a b := by
  constructor
  · intro h
    have hm := map_reachable_avoiding g.symm h
    simpa only [TreeAut.symm, Equiv.symm_apply_apply] using hm
  · exact map_reachable_avoiding g

theorem mem_cone_iff_map_mem_root_branch {d : ℕ} (g : TreeAut d)
    (r : TreeVertex d) (hr : r.1 ≠ []) (c : Fin d)
    (hp : g.toEquiv (parentVertex r) = ConnectedHull.root d)
    (hc : g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩) (u : TreeVertex d) :
    u ∈ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  let s : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  have hs : s.1 ≠ [] := by simp [s]
  have hparent : parentVertex s = ConnectedHull.root d := by
    apply Subtype.ext
    rfl
  have hmap := map_reachable_avoiding_iff g (parentVertex r) r u
  rw [hp, hc, ← hparent] at hmap
  rw [mem_cone_iff_reachable_avoiding_parent r u hr]
  change _ ↔ g.toEquiv u ∈ cone s
  rw [mem_cone_iff_reachable_avoiding_parent s (g.toEquiv u) hs]
  exact hmap.symm

theorem exists_reroot_cone {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∃ (g : TreeAut d) (c : Fin d),
      g.toEquiv (parentVertex r) = ConnectedHull.root d ∧
      g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩ ∧
      ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root (parentVertex r)
  have hadj := (g.map_adj (parentVertex r) r).mpr (treeAdj_parentVertex hr)
  rw [hg] at hadj
  obtain ⟨c, hc⟩ : ∃ c : Fin d, (g.toEquiv r).1 = [c] := by
    rcases hadj with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, by simpa using hc⟩
    · have hlen := congrArg List.length hc
      simp at hlen
  have hgr : g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩ := Subtype.ext hc
  exact ⟨g, c, hg, hgr, mem_cone_iff_map_mem_root_branch g r hr c hg hgr⟩

theorem exists_reroot_sideCone {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) :
    ∃ (g : TreeAut d) (c : Fin d),
      g.toEquiv (ConnectedHull.takeVertex v (i.1 + 1)) = ConnectedHull.root d ∧
      g.toEquiv (sideVertex hd v i) = ⟨[c], List.IsChain.singleton c⟩ ∧
      ∀ u : TreeVertex d, u ∈ cone (sideVertex hd v i) ↔
        [c] <+: (g.toEquiv u).1 := by
  have hr : (sideVertex hd v i).1 ≠ [] := by
    intro h
    have hl := sideVertex_length hd v i
    rw [h] at hl
    simp at hl
  simpa only [parent_sideVertex] using exists_reroot_cone (sideVertex hd v i) hr

end Problem367.PathSideBranches

end

end OAI

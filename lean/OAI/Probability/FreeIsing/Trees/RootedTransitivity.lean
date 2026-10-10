import OAI.Probability.FreeIsing.Estimates.LocalColorAutomorphisms
import OAI.Probability.FreeIsing.Trees.RootedGeometry
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

namespace Problem367

theorem exists_treeAut_map_common_stem {d : ℕ} (n : ℕ) :
    ∀ (stem s t : List (Fin d)) (_ : s.length = n) (_ : t.length = n)
      (hs : (stem ++ s).IsChain (· ≠ ·)) (_ : (stem ++ t).IsChain (· ≠ ·)),
    ∃ g : TreeAut d,
      (g.toEquiv ⟨stem ++ s, hs⟩).1 = stem ++ t ∧
      ∀ u : TreeVertex d, u.1.length ≤ stem.length → g.toEquiv u = u := by
  induction n with
  | zero =>
    intro stem s t hslen htlen hs ht
    have hs0 : s = [] := List.length_eq_zero_iff.mp hslen
    have ht0 : t = [] := List.length_eq_zero_iff.mp htlen
    subst s
    subst t
    exact ⟨TreeAut.refl d, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro stem s t hslen htlen hs ht
    cases s with
    | nil => simp at hslen
    | cons a s =>
      cases t with
      | nil => simp at htlen
      | cons b t =>
        have hslen' : s.length = n := by simpa using hslen
        have htlen' : t.length = n := by simpa using htlen
        let p : Equiv.Perm (Fin d) := Equiv.swap a b
        have hp : ∀ c ∈ stem.getLast?, p c = c := by
          intro c hc
          apply Equiv.swap_apply_of_ne_of_ne
          · exact (List.isChain_append.mp hs).2.2 c hc a (by simp)
          · exact (List.isChain_append.mp ht).2.2 c hc b (by simp)
        let g₁ := prefixColorAut stem p hp
        have hmid : ((stem ++ [b]) ++ s.map p).IsChain (· ≠ ·) := by
          have h := (g₁.toEquiv ⟨stem ++ a :: s, hs⟩).2
          change (prefixColorList stem p (stem ++ a :: s)).IsChain (· ≠ ·) at h
          simpa [prefixColorList_on_subtree, p, List.append_assoc] using h
        have htarget : ((stem ++ [b]) ++ t).IsChain (· ≠ ·) := by
          simpa only [List.append_assoc, List.singleton_append] using ht
        obtain ⟨g₂, hg₂, hfix₂⟩ := ih (stem ++ [b]) (s.map p) t
          (by simpa using hslen') htlen' hmid htarget
        refine ⟨g₁.trans g₂, ?_, ?_⟩
        · have hg₁ : g₁.toEquiv ⟨stem ++ a :: s, hs⟩ =
              ⟨(stem ++ [b]) ++ s.map p, hmid⟩ := by
            apply Subtype.ext
            simp [g₁, prefixColorList_on_subtree, p, List.append_assoc]
          change (g₂.toEquiv (g₁.toEquiv ⟨stem ++ a :: s, hs⟩)).1 = _
          rw [hg₁, hg₂]
          simp [List.append_assoc]
        · intro u hu
          change g₂.toEquiv (g₁.toEquiv u) = u
          have hfix₁ : g₁.toEquiv u = u := prefixColorAut_fixes_ball stem p hp u hu
          rw [hfix₁]
          apply hfix₂
          simp only [List.length_append, List.length_singleton]
          omega

theorem exists_rootFixing_treeAut_map {d : ℕ} (u v : TreeVertex d)
    (hlen : u.1.length = v.1.length) :
    ∃ g : TreeAut d, g.toEquiv u = v ∧
      g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩ := by
  obtain ⟨g, hmap, hfix⟩ := exists_treeAut_map_common_stem u.1.length
    [] u.1 v.1 rfl hlen.symm u.2 v.2
  refine ⟨g, ?_, hfix ⟨[], List.IsChain.nil⟩ (by simp)⟩
  apply Subtype.ext
  exact hmap

theorem exists_treeAut_map_adjacent_pair {d : ℕ} {u v x y : TreeVertex d}
    (huv : treeAdj u v) (hxy : treeAdj x y) :
    ∃ g : TreeAut d, g.toEquiv u = x ∧ g.toEquiv v = y := by
  let root : TreeVertex d := ⟨[], List.IsChain.nil⟩
  have root_neighbor_length : ∀ w : TreeVertex d, treeAdj root w → w.1.length = 1 := by
    intro w hw
    rcases hw with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hl := congrArg List.length hc
      simpa [root] using hl
    · have hl := congrArg List.length hc
      simp [root] at hl
  obtain ⟨g, hgu⟩ := exists_treeAut_to_root u
  obtain ⟨h, hhx⟩ := exists_treeAut_to_root x
  have hgv : (g.toEquiv v).1.length = 1 := by
    apply root_neighbor_length
    dsimp only [root]
    rw [← hgu]
    exact (g.map_adj u v).2 huv
  have hhy : (h.toEquiv y).1.length = 1 := by
    apply root_neighbor_length
    dsimp only [root]
    rw [← hhx]
    exact (h.map_adj x y).2 hxy
  obtain ⟨k, hkv, hkroot⟩ := exists_rootFixing_treeAut_map (g.toEquiv v) (h.toEquiv y)
    (hgv.trans hhy.symm)
  refine ⟨(g.trans k).trans h.symm, ?_, ?_⟩
  · change h.toEquiv.symm (k.toEquiv (g.toEquiv u)) = x
    rw [hgu, hkroot, ← hhx]
    exact h.toEquiv.symm_apply_apply x
  · change h.toEquiv.symm (k.toEquiv (g.toEquiv v)) = y
    rw [hkv]
    exact h.toEquiv.symm_apply_apply y

theorem rootFixing_treeAut_orbit_iff {d : ℕ} (u v : TreeVertex d) :
    (∃ g : TreeAut d, g.toEquiv u = v ∧
      g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩) ↔
      u.1.length = v.1.length := by
  constructor
  · rintro ⟨g, hmap, hroot⟩
    rw [← hmap]
    exact (treeAut_length_eq_of_root_fixed g hroot u).symm
  · exact exists_rootFixing_treeAut_map u v

theorem root_stabilizer_invariant_iff_radial {d : ℕ} {α : Type*}
    (f : TreeVertex d → α) :
    (∀ g : TreeAut d, g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩ →
      ∀ u, f (g.toEquiv u) = f u) ↔
    (∀ u v : TreeVertex d, u.1.length = v.1.length → f u = f v) := by
  constructor
  · intro hf u v hlen
    obtain ⟨g, hmap, hroot⟩ := exists_rootFixing_treeAut_map u v hlen
    simpa only [hmap] using (hf g hroot u).symm
  · intro hf g hroot u
    exact hf (g.toEquiv u) u (treeAut_length_eq_of_root_fixed g hroot u)

end Problem367

end OAI

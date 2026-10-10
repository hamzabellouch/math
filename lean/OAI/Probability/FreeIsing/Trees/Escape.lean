import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section

namespace Problem367
namespace TreeEscape

abbrev root {d : ℕ} : TreeVertex d := ⟨[], List.IsChain.nil⟩

private theorem adj_depth_le {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    u.1.length ≤ v.1.length + 1 := by
  rcases h with ⟨c, h⟩ | ⟨c, h⟩
  · have hlen := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  · have hlen := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hlen
    omega

theorem root_depth_le {d : ℕ} (g : TreeAut d) (v : TreeVertex d) :
    (g.toEquiv root).1.length ≤ (g.toEquiv v).1.length + v.1.length := by
  rcases v with ⟨w, hw⟩
  induction w using List.reverseRecOn with
  | nil => simp [root]
  | append_singleton w a ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.left_of_append
    have ih' := ih hw'
    change (g.toEquiv root).1.length ≤
      (g.toEquiv ⟨w, hw'⟩).1.length + w.length at ih'
    have hadj : treeAdj (⟨w, hw'⟩ : TreeVertex d) ⟨w ++ [a], hw⟩ :=
      Or.inl ⟨a, rfl⟩
    have hlen := adj_depth_le ((g.map_adj _ _).2 hadj)
    simp only [List.length_append, List.length_singleton]
    omega

theorem symm_root_depth {d : ℕ} (g : TreeAut d) :
    (g.toEquiv.symm root).1.length = (g.toEquiv root).1.length := by
  have h₁ := root_depth_le g (g.toEquiv.symm root)
  have h₂ := root_depth_le g.symm (g.toEquiv root)
  change (g.toEquiv.symm root).1.length ≤
    (g.toEquiv.symm (g.toEquiv root)).1.length + (g.toEquiv root).1.length at h₂
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    show (root : TreeVertex d).1.length = 0 from rfl, zero_add] at h₁ h₂
  exact Nat.le_antisymm h₂ h₁

theorem disjoint_image_of_root_depth {d : ℕ} (g : TreeAut d)
    (S T : Finset (TreeVertex d))
    (h : S.sup (fun v => v.1.length) + T.sup (fun v => v.1.length) <
      (g.toEquiv root).1.length) :
    Disjoint (S.image g.toEquiv) T := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hvt
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  have hlen := root_depth_le g u
  have hu' : u.1.length ≤ S.sup (fun v => v.1.length) :=
    Finset.le_sup (f := fun v : TreeVertex d => v.1.length) hu
  have hv' : (g.toEquiv u).1.length ≤ T.sup (fun v => v.1.length) :=
    Finset.le_sup (f := fun v : TreeVertex d => v.1.length) hvt
  omega

theorem disjoint_inverse_image_of_root_depth {d : ℕ} (g : TreeAut d)
    (S T : Finset (TreeVertex d))
    (h : S.sup (fun v => v.1.length) + T.sup (fun v => v.1.length) <
      (g.toEquiv root).1.length) :
    Disjoint (S.image g.toEquiv.symm) T := by
  apply disjoint_image_of_root_depth g.symm S T
  change _ < (g.toEquiv.symm root).1.length
  rwa [symm_root_depth]

def alternatingVertex {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : TreeVertex d :=
  ⟨List.ofFn (fun i : Fin n => (⟨i.1 % 2, by omega⟩ : Fin d)), by
    change List.IsChain (· ≠ ·) _
    rw [List.isChain_iff_getElem]
    intro i hi h
    have hi' : i + 1 < n := by simpa only [List.length_ofFn] using hi
    simp only [List.getElem_ofFn] at h
    have hv := congrArg Fin.val h
    simp only at hv
    omega⟩

@[simp] theorem alternatingVertex_depth {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    (alternatingVertex hd n).1.length = n := by
  simp [alternatingVertex]

def escapingAut {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : TreeAut d :=
  Classical.choose (exists_treeAut_map root (alternatingVertex hd n))

@[simp] theorem escapingAut_root {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    (escapingAut hd n).toEquiv root = alternatingVertex hd n :=
  Classical.choose_spec (exists_treeAut_map root (alternatingVertex hd n))

theorem disjoint_image_of_lt {d : ℕ} (hd : 2 ≤ d)
    (S T : Finset (TreeVertex d)) (n : ℕ)
    (hn : S.sup (fun v => v.1.length) + T.sup (fun v => v.1.length) < n) :
    Disjoint (S.image (escapingAut hd n).toEquiv) T := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hvt
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  have hlen := root_depth_le (escapingAut hd n) u
  rw [escapingAut_root, alternatingVertex_depth] at hlen
  have hu' : u.1.length ≤ S.sup (fun v => v.1.length) := Finset.le_sup (f := fun v : TreeVertex d => v.1.length) hu
  have hv' : ((escapingAut hd n).toEquiv u).1.length ≤
      T.sup (fun v => v.1.length) := Finset.le_sup (f := fun v : TreeVertex d => v.1.length) hvt
  omega

theorem eventually_disjoint_image {d : ℕ} (hd : 2 ≤ d)
    (S T : Finset (TreeVertex d)) :
    ∀ᶠ n in Filter.atTop, Disjoint (S.image (escapingAut hd n).toEquiv) T := by
  filter_upwards [Filter.eventually_gt_atTop
    (S.sup (fun v => v.1.length) + T.sup (fun v => v.1.length))] with n hn
  exact disjoint_image_of_lt hd S T n hn

theorem eventually_disjoint_inverse_image {d : ℕ} (hd : 2 ≤ d)
    (S T : Finset (TreeVertex d)) :
    ∀ᶠ n in Filter.atTop, Disjoint (S.image (escapingAut hd n).toEquiv.symm) T := by
  classical
  filter_upwards [eventually_disjoint_image hd T S] with n hn
  rw [Finset.disjoint_left] at hn ⊢
  intro v hv hvT
  obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
  have hgv : (escapingAut hd n).toEquiv v = u := by
    rw [← huv]
    exact (escapingAut hd n).toEquiv.apply_symm_apply u
  exact hn (Finset.mem_image.mpr ⟨v, hvT, hgv⟩) hu

end TreeEscape

theorem exists_treeAut_disjoint_finsets {d : ℕ} (hd : 2 ≤ d)
    (S T : Finset (TreeVertex d)) :
    ∃ g : TreeAut d, Disjoint (S.image g.toEquiv) T := by
  classical
  let n := S.sup (fun v => v.1.length) + T.sup (fun v => v.1.length) + 1
  exact ⟨TreeEscape.escapingAut hd n, TreeEscape.disjoint_image_of_lt hd S T n
    (Nat.lt_succ_self _)⟩
end Problem367

end

end OAI

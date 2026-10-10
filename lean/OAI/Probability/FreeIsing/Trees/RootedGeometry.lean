import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

namespace Problem367

private theorem image_child_depth_le {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) : v.1.length ≤ u.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hh := congrArg List.length hc
    simp only [List.length_append, List.length_singleton] at hh
    omega
  · have hh := congrArg List.length hc
    simp only [List.length_append, List.length_singleton] at hh
    omega

private theorem image_depth_le_of_root_fixed {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩)
    (u : TreeVertex d) : (g.toEquiv u).1.length ≤ u.1.length := by
  rcases u with ⟨w, hw⟩
  induction w using List.reverseRecOn with
  | nil => simpa only [hg, List.length_nil] using (Nat.le_refl 0)
  | append_singleton w c ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.left_of_append
    have hparent := ih hw'
    change (g.toEquiv ⟨w, hw'⟩).1.length ≤ w.length at hparent
    have hadj : treeAdj (⟨w, hw'⟩ : TreeVertex d) ⟨w ++ [c], hw⟩ := Or.inl ⟨c, rfl⟩
    have hchild := image_child_depth_le ((g.map_adj _ _).2 hadj)
    simp only [List.length_append, List.length_singleton]
    omega

theorem treeAut_length_eq_of_root_fixed {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩)
    (u : TreeVertex d) : (g.toEquiv u).1.length = u.1.length := by
  apply Nat.le_antisymm (image_depth_le_of_root_fixed g hg u)
  have hsym : g.symm.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩ := by
    change g.toEquiv.symm ⟨[], List.IsChain.nil⟩ = _
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hg]
  have h := image_depth_le_of_root_fixed g.symm hsym (g.toEquiv u)
  simpa only [TreeAut.symm, Equiv.symm_apply_apply] using h

theorem treeAut_preimage_depthBall {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩) (R : ℕ) :
    g.toEquiv ⁻¹' {u : TreeVertex d | u.1.length ≤ R} =
      {u : TreeVertex d | u.1.length ≤ R} := by
  ext u
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, treeAut_length_eq_of_root_fixed g hg]

theorem treeAut_image_depthBall {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩) (R : ℕ) :
    g.toEquiv '' {u : TreeVertex d | u.1.length ≤ R} =
      {u : TreeVertex d | u.1.length ≤ R} := by
  calc
    g.toEquiv '' {u : TreeVertex d | u.1.length ≤ R} =
        g.toEquiv '' (g.toEquiv ⁻¹' {u : TreeVertex d | u.1.length ≤ R}) :=
      congrArg (fun S : Set (TreeVertex d) => g.toEquiv '' S)
        (treeAut_preimage_depthBall g hg R).symm
    _ = _ := Set.image_preimage_eq _ g.toEquiv.surjective

theorem treeAut_preimage_depthSphere {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv ⟨[], List.IsChain.nil⟩ = ⟨[], List.IsChain.nil⟩) (R : ℕ) :
    g.toEquiv ⁻¹' {u : TreeVertex d | u.1.length = R} =
      {u : TreeVertex d | u.1.length = R} := by
  ext u
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, treeAut_length_eq_of_root_fixed g hg]

end Problem367

end OAI

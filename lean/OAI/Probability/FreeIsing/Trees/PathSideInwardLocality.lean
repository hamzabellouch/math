import OAI.Probability.FreeIsing.Trees.PathSideBranches

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

theorem sideCone_subset_earlier_outgoing {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) {i j : Fin v.1.length} (hji : j < i) :
    cone (sideVertex hd v i) ⊆
      cone (ConnectedHull.takeVertex v (j.1 + 2)) := by
  apply (sideCone_subset_forward hd v i).trans
  apply cone_mono
  change v.1.take (j.1 + 2) <+: v.1.take (i.1 + 1)
  exact List.take_prefix_take_left (by omega)

theorem earlier_inward_subset_side_complement {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) (r : TreeVertex d)
    {i j : Fin v.1.length} (hji : j < i) :
    cone r \ cone (ConnectedHull.takeVertex v (j.1 + 2)) ⊆
      (cone (sideVertex hd v i))ᶜ := by
  intro u hu hs
  exact hu.2 (sideCone_subset_earlier_outgoing hd v hji hs)

theorem sideCone_disjoint_earlier_inward {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) (r : TreeVertex d)
    {i j : Fin v.1.length} (hji : j < i) :
    Disjoint (cone (sideVertex hd v i))
      (cone r \ cone (ConnectedHull.takeVertex v (j.1 + 2))) := by
  apply Set.disjoint_left.mpr
  intro u hs hu
  exact earlier_inward_subset_side_complement hd v r hji hu hs

theorem sideCone_disjoint_outgoing {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) (i : Fin v.1.length) (hi : i.1 + 1 < v.1.length) :
    Disjoint (cone (sideVertex hd v i))
      (cone (ConnectedHull.takeVertex v (i.1 + 2))) := by
  exact sideCone_disjoint_later_forward hd v
    (j := ⟨i.1 + 1, hi⟩) (by exact Nat.lt_succ_self i.1)

theorem sideCone_subset_inward {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) (r : TreeVertex d) (i : Fin v.1.length)
    (hr : r.1 <+: (ConnectedHull.takeVertex v (i.1 + 1)).1)
    (hi : i.1 + 1 < v.1.length) :
    cone (sideVertex hd v i) ⊆
      cone r \ cone (ConnectedHull.takeVertex v (i.1 + 2)) := by
  intro u hu
  exact ⟨cone_mono hr (sideCone_subset_forward hd v i hu),
    Set.disjoint_left.mp (sideCone_disjoint_outgoing hd v i hi) hu⟩

theorem target_mem_inward_without_side {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) (r : TreeVertex d) (i : Fin v.1.length)
    (hr : r.1 <+: (ConnectedHull.takeVertex v (i.1 + 1)).1)
    (hi : i.1 + 1 < v.1.length) :
    ConnectedHull.takeVertex v (i.1 + 1) ∈
      (cone r \ cone (ConnectedHull.takeVertex v (i.1 + 2))) \
        cone (sideVertex hd v i) := by
  refine ⟨⟨hr, ?_⟩, path_vertex_not_mem_sideCone hd v i _⟩
  intro h
  have hl := h.length_le
  change (v.1.take (i.1 + 2)).length ≤ (v.1.take (i.1 + 1)).length at hl
  simp only [List.length_take] at hl
  omega

end Problem367.PathSideBranches

end

end OAI

import OAI.Probability.FreeIsing.Trees.Parents

namespace OAI

namespace Problem367

private lemma mem_inducedEdges_8911 {d : ℕ} (D : Finset (TreeVertex d))
    (u v : TreeVertex d) :
    (u, v) ∈ inducedEdges D ↔
      (u ∈ D ∧ v ∈ D) ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  rw [inducedEdges, Finset.mem_filter]
  exact and_congr Finset.mem_product Iff.rfl

lemma inducedEdges_snd_injOn {d : ℕ} (D : Finset (TreeVertex d)) :
    Set.InjOn Prod.snd (↑(inducedEdges D) : Set (TreeVertex d × TreeVertex d)) := by
  rintro ⟨a, b⟩ hab ⟨c, e⟩ hce heq
  have hab' : (a ∈ D ∧ b ∈ D) ∧ treeAdj a b ∧ a.1.length < b.1.length := by
    exact (mem_inducedEdges_8911 D a b).mp hab
  have hce' : (c ∈ D ∧ e ∈ D) ∧ treeAdj c e ∧ c.1.length < e.1.length := by
    exact (mem_inducedEdges_8911 D c e).mp hce
  change b = e at heq
  subst e
  exact Prod.ext (treeAdj_lower_unique hab'.2.1 hce'.2.1 hab'.2.2 hce'.2.2) rfl

lemma ConnectedFinset.inducedEdges_image_snd {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    (inducedEdges D).image Prod.snd = D.erase r := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨⟨u, w⟩, huw, hwv⟩ := Finset.mem_image.mp hv
    have huw' : (u ∈ D ∧ w ∈ D) ∧ treeAdj u w ∧ u.1.length < w.1.length := by
      exact (mem_inducedEdges_8911 D u w).mp huw
    change w = v at hwv
    subst w
    apply Finset.mem_erase.mpr
    refine ⟨?_, huw'.1.2⟩
    intro heq
    subst v
    have := hmin u huw'.1.1
    omega
  · intro hv
    obtain ⟨hne, hv⟩ := Finset.mem_erase.mp hv
    apply Finset.mem_image.mpr
    refine ⟨(parentVertex v, v), ?_, rfl⟩
    have hp := hD.parent_mem_of_ne_min hr hmin hv hne
    have hnil := ConnectedFinset.ne_nil_of_ne_min hmin hv hne
    have hpos : 0 < v.1.length := List.length_pos_iff.mpr hnil
    have hadj := treeAdj_parentVertex hnil
    apply (mem_inducedEdges_8911 D _ _).mpr
    refine ⟨⟨hp, hv⟩, hadj, ?_⟩
    rw [parentVertex_length]
    omega

lemma ConnectedFinset.inducedEdges_card_add_one {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) :
    (inducedEdges D).card + 1 = D.card := by
  classical
  obtain ⟨r, hr, hmin⟩ := D.exists_min_image (fun v => v.1.length) hD.1
  have himage := hD.inducedEdges_image_snd hr hmin
  have hcard := congrArg Finset.card himage
  rw [Finset.card_image_of_injOn (inducedEdges_snd_injOn D), Finset.card_erase_of_mem hr] at hcard
  have hpos : 0 < D.card := Finset.card_pos.mpr hD.1
  omega

lemma ConnectedFinset.inducedEdges_card {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) :
    (inducedEdges D).card = D.card - 1 := by
  have := hD.inducedEdges_card_add_one
  omega

end Problem367

end OAI

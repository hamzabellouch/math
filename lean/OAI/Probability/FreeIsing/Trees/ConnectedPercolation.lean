import OAI.Probability.FreeIsing.Trees.Parents

namespace OAI

noncomputable section

namespace Problem367.ConnectedPercolation

def deepestVertexOr {d : ℕ} (r : TreeVertex d) (S : Finset (TreeVertex d)) : TreeVertex d :=
  if h : S.Nonempty then
    Classical.choose (S.exists_max_image (fun v => v.1.length) h)
  else r

lemma deepestVertexOr_mem {d : ℕ} (r : TreeVertex d) (S : Finset (TreeVertex d))
    (h : S.Nonempty) : deepestVertexOr r S ∈ S := by
  rw [deepestVertexOr, dite_eq_left h]
  exact (Classical.choose_spec (S.exists_max_image (fun v => v.1.length) h)).1

lemma le_deepestVertexOr_length {d : ℕ} (r : TreeVertex d)
    (S : Finset (TreeVertex d)) (h : S.Nonempty)
    {v : TreeVertex d} (hv : v ∈ S) : v.1.length ≤ (deepestVertexOr r S).1.length := by
  rw [deepestVertexOr, dite_eq_left h]
  exact (Classical.choose_spec (S.exists_max_image (fun v => v.1.length) h)).2 v hv

def prefixCandidates {d : ℕ} (D : Finset (TreeVertex d)) (x : TreeVertex d) :
    Finset (TreeVertex d) := by
  classical
  exact D.filter (fun v => v.1 <+: x.1)

@[simp] lemma mem_prefixCandidates {d : ℕ} (D : Finset (TreeVertex d))
    (x v : TreeVertex d) : v ∈ prefixCandidates D x ↔ v ∈ D ∧ v.1 <+: x.1 := by
  classical
  simp [prefixCandidates]

def gate {d : ℕ} (D : Finset (TreeVertex d)) (r x : TreeVertex d) : TreeVertex d :=
  deepestVertexOr r (prefixCandidates D x)

lemma gate_of_mem {d : ℕ} {D : Finset (TreeVertex d)} (r : TreeVertex d)
    {x : TreeVertex d} (hx : x ∈ D) : gate D r x = x := by
  have hx' : x ∈ prefixCandidates D x :=
    (mem_prefixCandidates D x x).mpr ⟨hx, List.prefix_refl _⟩
  have hne : (prefixCandidates D x).Nonempty := ⟨x, hx'⟩
  have hmem := (mem_prefixCandidates D x _).mp
    (deepestVertexOr_mem r (prefixCandidates D x) hne)
  exact Subtype.ext (hmem.2.eq_of_length_le
    (le_deepestVertexOr_length r (prefixCandidates D x) hne hx'))

lemma gate_of_no_prefix {d : ℕ} {D : Finset (TreeVertex d)} (r x : TreeVertex d)
    (h : ∀ v ∈ D, ¬v.1 <+: x.1) : gate D r x = r := by
  have hempty : prefixCandidates D x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvD, hvx⟩ := (mem_prefixCandidates D x v).mp hv
    exact h v hvD hvx
  simp [gate, hempty, deepestVertexOr]

lemma prefixCandidates_append_of_not_mem {d : ℕ} (D : Finset (TreeVertex d))
    {x y : TreeVertex d} {c : Fin d} (hxy : y.1 = x.1 ++ [c]) (hy : y ∉ D) :
    prefixCandidates D x = prefixCandidates D y := by
  classical
  ext v
  simp only [mem_prefixCandidates]
  constructor
  · rintro ⟨hv, hvx⟩
    refine ⟨hv, hvx.trans ?_⟩
    rw [hxy]
    exact List.prefix_append _ _
  · rintro ⟨hv, hvy⟩
    refine ⟨hv, ?_⟩
    have hne : v ≠ y := fun h => hy (h ▸ hv)
    have hlt : v.1.length < y.1.length := by
      have hle := hvy.length_le
      have hneq : v.1.length ≠ y.1.length :=
        fun h => hne (Subtype.ext (hvy.eq_of_length h))
      omega
    apply List.prefix_of_prefix_length_le hvy
    · rw [hxy]
      exact List.prefix_append _ _
    · have hlen : y.1.length = x.1.length + 1 := by simp [hxy]
      omega

lemma gate_append_cases {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    {x y : TreeVertex d} {c : Fin d} (hxy : y.1 = x.1 ++ [c]) :
    (x ∈ D ∧ y ∈ D) ∨ gate D r x = gate D r y := by
  classical
  by_cases hy : y ∈ D
  · by_cases hx : x ∈ D
    · exact Or.inl ⟨hx, hy⟩
    · right
      have hp : parentVertex y = x := by
        apply Subtype.ext
        simp [parentVertex, hxy]
      have hyr : y = r := by
        by_contra hne
        exact hx (hp ▸ hD.parent_mem_of_ne_min hr hmin hy hne)
      rw [gate_of_mem r hy, hyr]
      apply gate_of_no_prefix
      intro v hv hvx
      have hlen : r.1.length = x.1.length + 1 := by rw [← hyr]; simp [hxy]
      have hvlen := hvx.length_le
      have hrlen := hmin v hv
      omega
  · right
    unfold gate
    rw [prefixCandidates_append_of_not_mem D hxy hy]

lemma gate_adj_cases {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    {x y : TreeVertex d} (hxy : treeAdj x y) :
    (x ∈ D ∧ y ∈ D) ∨ gate D r x = gate D r y := by
  rcases hxy with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact gate_append_cases hD hr hmin hc
  · rcases gate_append_cases hD hr hmin hc with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

end Problem367.ConnectedPercolation

namespace Problem367

theorem ConnectedFinset.reflTransGen_restrict_iff {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {R : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ ⦃x y⦄, R x y → treeAdj x y)
    {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D) :
    Relation.ReflTransGen R u v ↔
      Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ R x y) u v := by
  constructor
  · intro h
    obtain ⟨r, hr, hmin⟩ := D.exists_min_image (fun w => w.1.length) hD.1
    let π := ConnectedPercolation.gate D r
    have hmap : ∀ ⦃x y⦄, Relation.ReflTransGen R x y →
        Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ R a b) (π x) (π y) := by
      intro x y hxy
      induction hxy with
      | refl => exact .refl
      | @tail y z hxy hyz ih =>
          rcases ConnectedPercolation.gate_adj_cases hD hr hmin (hR hyz) with hmem | heq
          · have hπy : π y = y := ConnectedPercolation.gate_of_mem r hmem.1
            have hπz : π z = z := ConnectedPercolation.gate_of_mem r hmem.2
            rw [hπy] at ih
            rw [hπz]
            exact ih.tail ⟨hmem.1, hmem.2, hyz⟩
          · change π y = π z at heq
            exact heq ▸ ih
    simpa only [π, ConnectedPercolation.gate_of_mem r hu,
      ConnectedPercolation.gate_of_mem r hv] using hmap h
  · intro h
    exact Relation.ReflTransGen.mono
      (fun x y (h : x ∈ D ∧ y ∈ D ∧ R x y) => h.2.2) u v h

theorem ConnectedFinset.cluster_inter_eq {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {R : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ ⦃x y⦄, R x y → treeAdj x y)
    {u : TreeVertex d} (hu : u ∈ D) :
    {v | Relation.ReflTransGen R u v} ∩ (D : Set (TreeVertex d)) =
      {v | Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ R x y) u v} := by
  ext v
  constructor
  · rintro ⟨hp, hv⟩
    exact (hD.reflTransGen_restrict_iff hR hu hv).mp hp
  · intro hp
    have hv : v ∈ D := by
      induction hp with
      | refl => exact hu
      | tail _ h _ => exact h.2.1
    exact ⟨(hD.reflTransGen_restrict_iff hR hu hv).mpr hp, hv⟩

end Problem367

end

end OAI

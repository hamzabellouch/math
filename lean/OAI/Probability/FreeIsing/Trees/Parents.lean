import OAI.Probability.FreeIsing.Model

namespace OAI

namespace Problem367

def parentVertex {d : ℕ} (v : TreeVertex d) : TreeVertex d :=
  ⟨v.1.dropLast, v.2.dropLast⟩

@[simp] theorem parentVertex_val {d : ℕ} (v : TreeVertex d) :
    (parentVertex v).1 = v.1.dropLast := rfl

@[simp] theorem parentVertex_length {d : ℕ} (v : TreeVertex d) :
    (parentVertex v).1.length = v.1.length - 1 := by
  simp [parentVertex]

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_lower_unique {d : ℕ} {u v w : TreeVertex d}
    (hu : treeAdj u w) (hv : treeAdj v w)
    (huw : u.1.length < w.1.length) (hvw : v.1.length < w.1.length) : u = v := by
  exact (treeAdj_parent_of_length_lt hu huw).symm.trans
    (treeAdj_parent_of_length_lt hv hvw)

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

theorem treeAdj_preserves_prefix {d : ℕ} {r u v : TreeVertex d}
    (hu : r.1 <+: u.1) (h : treeAdj u v) (hne : u ≠ r) : r.1 <+: v.1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [hc]
    exact hu.trans (List.prefix_append _ _)
  · have hlen : r.1.length < u.1.length := by
      have hle := hu.length_le
      have hneq : r.1.length ≠ u.1.length := by
        intro heq
        exact hne (Subtype.ext (hu.eq_of_length heq).symm)
      omega
    have hv : v.1 <+: u.1 := by
      rw [hc]
      exact List.prefix_append _ _
    apply List.prefix_of_prefix_length_le hu hv
    have hlen' : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_preserves_prefix_of_parent_not_mem {d : ℕ}
    {D : Finset (TreeVertex d)} {r u v : TreeVertex d}
    (hr : parentVertex r ∉ D) (hv : v ∈ D)
    (hu : r.1 <+: u.1) (h : treeAdj u v) : r.1 <+: v.1 := by
  by_cases hne : u = r
  · subst u
    rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [hc]
      exact List.prefix_append _ _
    · have heq : parentVertex r = v := by
        apply Subtype.ext
        simp [parentVertex, hc]
      exact False.elim (hr (heq.symm ▸ hv))
  · exact treeAdj_preserves_prefix hu h hne

theorem prefix_of_reachable_of_parent_not_mem {d : ℕ}
    {D : Finset (TreeVertex d)} {r v : TreeVertex d}
    (hr : parentVertex r ∉ D)
    (h : Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ D ∧ y ∈ D ∧ treeAdj x y) r v) :
    r.1 <+: v.1 := by
  induction h with
  | refl => exact List.prefix_refl _
  | tail h hab ih =>
      exact treeAdj_preserves_prefix_of_parent_not_mem hr hab.2.1 ih hab.2.2

theorem ConnectedFinset.parent_mem_of_ne_min {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r v : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (hv : v ∈ D) (hne : v ≠ r) : parentVertex v ∈ D := by
  by_contra hp
  have hpre := prefix_of_reachable_of_parent_not_mem hp (hD.2 v hv r hr)
  exact hne (Subtype.ext (hpre.eq_of_length_le (hmin v hv)))

theorem ConnectedFinset.ne_nil_of_ne_min {d : ℕ}
    {D : Finset (TreeVertex d)} {r v : TreeVertex d}
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (hv : v ∈ D) (hne : v ≠ r) : v.1 ≠ [] := by
  intro heq
  have hrlen : r.1.length = 0 := by
    have := hmin v hv
    rw [heq, List.length_nil] at this
    omega
  have hre : r.1 = [] := List.length_eq_zero_iff.mp hrlen
  exact hne (Subtype.ext (heq.trans hre.symm))

theorem ConnectedFinset.min_prefix {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r v : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (hv : v ∈ D) : r.1 <+: v.1 := by
  by_cases hnil : r.1 = []
  · rw [hnil]
    exact List.nil_prefix
  · have hp : parentVertex r ∉ D := by
      intro hp
      have hlen := hmin (parentVertex r) hp
      have hpos : 0 < r.1.length := List.length_pos_iff.mpr hnil
      rw [parentVertex_length] at hlen
      omega
    exact prefix_of_reachable_of_parent_not_mem hp (hD.2 r hr v hv)

theorem ConnectedFinset.min_unique {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r v : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (hv : v ∈ D) (hle : v.1.length ≤ r.1.length) : v = r := by
  exact Subtype.ext ((hD.min_prefix hr hmin hv).eq_of_length_le hle).symm

theorem ConnectedFinset.prefix_mem_of_min_length_le {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    {u v : TreeVertex d} (hv : v ∈ D) (huv : u.1 <+: v.1)
    (hru : r.1.length ≤ u.1.length) : u ∈ D := by
  have aux : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → v ∈ D →
      u.1 <+: v.1 → u ∈ D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn hv huv
      by_cases huv_eq : u = v
      · exact huv_eq.symm ▸ hv
      · have hvne : v ≠ r := by
          intro heq
          subst v
          exact huv_eq (Subtype.ext (huv.eq_of_length_le hru))
        have hp := hD.parent_mem_of_ne_min hr hmin hv hvne
        have hvnil := ConnectedFinset.ne_nil_of_ne_min hmin hv hvne
        have hpos : 0 < v.1.length := List.length_pos_iff.mpr hvnil
        have hplen : (parentVertex v).1.length < n := by
          rw [parentVertex_length]
          omega
        have hup : u.1 <+: (parentVertex v).1 := by
          apply List.prefix_of_prefix_length_le huv (List.dropLast_prefix v.1)
          have hle := huv.length_le
          have hneq : u.1.length ≠ v.1.length := by
            intro heq
            exact huv_eq (Subtype.ext (huv.eq_of_length heq))
          change u.1.length ≤ (parentVertex v).1.length
          rw [parentVertex_length]
          omega
        exact ih _ hplen _ rfl hp hup
  exact aux _ v rfl hv huv

end Problem367

end OAI

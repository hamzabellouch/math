import OAI.Probability.FreeIsing.Trees.ConnectedExhaustion
import OAI.Probability.FreeIsing.Trees.Parents

namespace OAI

noncomputable section

namespace Problem367

def rootComponentFinset {d : ℕ} (D : Finset (TreeVertex d)) (c : Fin d) :
    Finset (TreeVertex d) := by
  classical
  exact D.filter (fun v => [c] <+: v.1)

def rootComplementFinset {d : ℕ} (D : Finset (TreeVertex d)) (c : Fin d) :
    Finset (TreeVertex d) := by
  classical
  exact D.filter (fun v => ¬ [c] <+: v.1)

@[simp] theorem mem_rootComponentFinset {d : ℕ} {D : Finset (TreeVertex d)}
    {c : Fin d} {v : TreeVertex d} : v ∈ rootComponentFinset D c ↔
      v ∈ D ∧ [c] <+: v.1 := by
  classical
  simp [rootComponentFinset]

@[simp] theorem mem_rootComplementFinset {d : ℕ} {D : Finset (TreeVertex d)}
    {c : Fin d} {v : TreeVertex d} : v ∈ rootComplementFinset D c ↔
      v ∈ D ∧ ¬ [c] <+: v.1 := by
  classical
  simp [rootComplementFinset]

theorem ConnectedFinset.prefix_mem_of_root_mem {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hroot : ConnectedHull.root d ∈ D) {u v : TreeVertex d}
    (hv : v ∈ D) (huv : u.1 <+: v.1) : u ∈ D :=
  hD.prefix_mem_of_min_length_le hroot (fun _ _ => Nat.zero_le _) hv huv (Nat.zero_le _)

theorem ConnectedFinset.filter_prefix_connected {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hroot : ConnectedHull.root d ∈ D) (r : TreeVertex d) (hr : r ∈ D) :
    ConnectedFinset (D.filter (fun v => r.1 <+: v.1)) := by
  classical
  let E := D.filter (fun v => r.1 <+: v.1)
  have hrE : r ∈ E := Finset.mem_filter.mpr ⟨hr, List.prefix_refl _⟩
  let R := fun x y : TreeVertex d => x ∈ E ∧ y ∈ E ∧ treeAdj x y
  have paths : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → v ∈ E →
      Relation.ReflTransGen R r v ∧ Relation.ReflTransGen R v r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn hv
      by_cases heq : v = r
      · subst v
        exact ⟨.refl, .refl⟩
      have hv' := Finset.mem_filter.mp hv
      have hnil : v.1 ≠ [] := by
        intro he
        have hre : r.1 = [] := by
          have hlen : r.1.length ≤ 0 := by simpa only [he, List.length_nil] using hv'.2.length_le
          exact List.length_eq_zero_iff.mp (by omega)
        exact heq (Subtype.ext (he.trans hre.symm))
      have hadj := treeAdj_parentVertex hnil
      have hpD : parentVertex v ∈ D :=
        hD.prefix_mem_of_root_mem hroot hv'.1 (List.dropLast_prefix v.1)
      have hpE : parentVertex v ∈ E := Finset.mem_filter.mpr
        ⟨hpD, treeAdj_preserves_prefix hv'.2 hadj.symm heq⟩
      have hlt : (parentVertex v).1.length < n := by
        have hpos := List.length_pos_iff.mpr hnil
        rw [parentVertex_length]
        omega
      obtain ⟨hforward, hbackward⟩ := ih _ hlt _ rfl hpE
      exact ⟨hforward.trans (.single ⟨hpE, hv, hadj⟩),
        (Relation.ReflTransGen.single ⟨hv, hpE, hadj.symm⟩).trans hbackward⟩
  refine ⟨⟨r, hrE⟩, ?_⟩
  intro u hu v hv
  exact (paths _ u rfl hu).2.trans (paths _ v rfl hv).1

theorem ConnectedFinset.filter_not_prefix_connected {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hroot : ConnectedHull.root d ∈ D) (r : TreeVertex d) (hr : r.1 ≠ []) :
    ConnectedFinset (D.filter (fun v => ¬ r.1 <+: v.1)) := by
  classical
  let E := D.filter (fun v => ¬ r.1 <+: v.1)
  have hrootE : ConnectedHull.root d ∈ E := by
    apply Finset.mem_filter.mpr
    exact ⟨hroot, by simpa [ConnectedHull.root] using hr⟩
  have paths (v : TreeVertex d) (hv : v ∈ E) :
      Relation.ReflTransGen
        (fun x y : TreeVertex d => x ∈ E ∧ y ∈ E ∧ treeAdj x y)
        (ConnectedHull.root d) v ∧
      Relation.ReflTransGen
        (fun x y : TreeVertex d => x ∈ E ∧ y ∈ E ∧ treeAdj x y)
        v (ConnectedHull.root d) := by
    have hp : ∀ n ≤ v.1.length, ConnectedHull.takeVertex v n ∈ E := by
      intro n hn
      apply Finset.mem_filter.mpr
      refine ⟨hD.prefix_mem_of_root_mem hroot (Finset.mem_filter.mp hv).1
        (List.take_prefix n v.1), ?_⟩
      intro hpre
      exact (Finset.mem_filter.mp hv).2 (hpre.trans (List.take_prefix n v.1))
    simpa only [ConnectedHull.prefix_length] using
      ConnectedHull.prefix_paths E v hp (Nat.le_refl v.1.length)
  refine ⟨⟨ConnectedHull.root d, hrootE⟩, ?_⟩
  intro u hu v hv
  exact (paths u hu).2.trans (paths v hv).1

theorem rootComponentFinset_connected {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) :
    ConnectedFinset (rootComponentFinset D c) :=
  hD.filter_prefix_connected hroot ⟨[c], List.IsChain.singleton c⟩ hc

theorem rootComplementFinset_connected {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hroot : ConnectedHull.root d ∈ D) (c : Fin d) :
    ConnectedFinset (rootComplementFinset D c) :=
  hD.filter_not_prefix_connected hroot ⟨[c], List.IsChain.singleton c⟩ (by simp)

theorem rootComponentFinset_union_complement {d : ℕ} (D : Finset (TreeVertex d))
    (c : Fin d) : rootComponentFinset D c ∪ rootComplementFinset D c = D := by
  classical
  ext v
  simp only [Finset.mem_union, mem_rootComponentFinset, mem_rootComplementFinset]
  tauto

theorem rootComponentFinset_disjoint_complement {d : ℕ} (D : Finset (TreeVertex d))
    (c : Fin d) : Disjoint (rootComponentFinset D c) (rootComplementFinset D c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (mem_rootComplementFinset.mp hw).2 (mem_rootComponentFinset.mp hv).2

theorem root_component_crossing_edge {d : ℕ} {c : Fin d} {u v : TreeVertex d}
    (hu : [c] <+: u.1) (hv : ¬ [c] <+: v.1) (hadj : treeAdj u v) :
    u = ⟨[c], List.IsChain.singleton c⟩ ∧ v = ConnectedHull.root d := by
  have hueq : u = (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) := by
    by_contra hne
    exact hv (treeAdj_preserves_prefix (r := ⟨[c], List.IsChain.singleton c⟩) hu hadj hne)
  refine ⟨hueq, ?_⟩
  subst u
  rcases hadj with ⟨a, ha⟩ | ⟨a, ha⟩
  · exfalso
    apply hv
    rw [ha]
    exact List.prefix_append _ _
  · apply Subtype.ext
    change v.1 = []
    have hlen := congrArg List.length ha
    simp only [List.length_singleton, List.length_append] at hlen
    exact List.length_eq_zero_iff.mp (by omega)

theorem rootComponentFinset_mono {d : ℕ} (c : Fin d) :
    Monotone (fun D : Finset (TreeVertex d) => rootComponentFinset D c) := by
  intro D E hDE v hv
  exact mem_rootComponentFinset.mpr ⟨hDE (mem_rootComponentFinset.mp hv).1,
    (mem_rootComponentFinset.mp hv).2⟩

theorem rootComplementFinset_mono {d : ℕ} (c : Fin d) :
    Monotone (fun D : Finset (TreeVertex d) => rootComplementFinset D c) := by
  intro D E hDE v hv
  exact mem_rootComplementFinset.mpr ⟨hDE (mem_rootComplementFinset.mp hv).1,
    (mem_rootComplementFinset.mp hv).2⟩

theorem rootComponentFinset_exhausts {d : ℕ} (D : ℕ → Finset (TreeVertex d))
    (hex : ∀ v, ∃ n, v ∈ D n) (c : Fin d) (v : TreeVertex d)
    (hv : [c] <+: v.1) : ∃ n, v ∈ rootComponentFinset (D n) c := by
  obtain ⟨n, hn⟩ := hex v
  exact ⟨n, mem_rootComponentFinset.mpr ⟨hn, hv⟩⟩

theorem singleton_prefix_iff_cons {d : ℕ} (c : Fin d) (v : TreeVertex d) :
    [c] <+: v.1 ↔ ∃ w, v.1 = c :: w := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, hw.symm⟩

theorem rootComponentFinset_eq_filter {d : ℕ} (D : Finset (TreeVertex d)) (c : Fin d) :
    rootComponentFinset D c = (by
      classical
      exact D.filter (fun v => ∃ w, v.1 = c :: w)) := by
  classical
  ext v
  simp only [mem_rootComponentFinset, Finset.mem_filter, singleton_prefix_iff_cons]

theorem rootComplementFinset_eq_sdiff {d : ℕ} (D : Finset (TreeVertex d)) (c : Fin d) :
    rootComplementFinset D c = D \ rootComponentFinset D c := by
  classical
  ext v
  simp only [mem_rootComplementFinset, Finset.mem_sdiff, mem_rootComponentFinset]
  tauto

theorem rootComponentFinset_root_mem {d : ℕ} {D : Finset (TreeVertex d)} (c : Fin d)
    (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) :
    (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ rootComponentFinset D c :=
  mem_rootComponentFinset.mpr ⟨hc, List.prefix_refl _⟩

theorem rootComplementFinset_root_mem {d : ℕ} {D : Finset (TreeVertex d)} (c : Fin d)
    (hroot : ConnectedHull.root d ∈ D) :
    ConnectedHull.root d ∈ rootComplementFinset D c := by
  apply mem_rootComplementFinset.mpr
  refine ⟨hroot, ?_⟩
  intro h
  have hlen := h.length_le
  change 1 ≤ 0 at hlen
  omega

private theorem mem_inducedEdges_cut {d : ℕ} {D : Finset (TreeVertex d)}
    {u v : TreeVertex d} : (u, v) ∈ inducedEdges D ↔
      u ∈ D ∧ v ∈ D ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  simp [inducedEdges, and_assoc]

theorem inducedEdges_rootComponent_split {d : ℕ} {D : Finset (TreeVertex d)}
    (hroot : ConnectedHull.root d ∈ D) (c : Fin d)
    (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) :
    inducedEdges D = insert (ConnectedHull.root d, ⟨[c], List.IsChain.singleton c⟩)
      (inducedEdges (rootComponentFinset D c) ∪ inducedEdges (rootComplementFinset D c)) := by
  classical
  ext ⟨u, v⟩
  constructor
  · intro he
    obtain ⟨hu, hv, hadj, hlen⟩ := mem_inducedEdges_cut.mp he
    by_cases hcu : [c] <+: u.1
    · by_cases hcv : [c] <+: v.1
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_union.mpr
        exact Or.inl (mem_inducedEdges_cut.mpr
          ⟨mem_rootComponentFinset.mpr ⟨hu, hcu⟩,
            mem_rootComponentFinset.mpr ⟨hv, hcv⟩, hadj, hlen⟩)
      · obtain ⟨rfl, rfl⟩ := root_component_crossing_edge hcu hcv hadj
        change 1 < 0 at hlen
        omega
    · by_cases hcv : [c] <+: v.1
      · obtain ⟨rfl, rfl⟩ := root_component_crossing_edge hcv hcu hadj.symm
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_union.mpr
        exact Or.inr (mem_inducedEdges_cut.mpr
          ⟨mem_rootComplementFinset.mpr ⟨hu, hcu⟩,
            mem_rootComplementFinset.mpr ⟨hv, hcv⟩, hadj, hlen⟩)
  · intro he
    rcases Finset.mem_insert.mp he with heq | he
    · have hu : u = ConnectedHull.root d := congrArg Prod.fst heq
      have hv : v = (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) := congrArg Prod.snd heq
      subst u
      subst v
      exact mem_inducedEdges_cut.mpr ⟨hroot, hc, Or.inl ⟨c, rfl⟩, by change 0 < 1; omega⟩
    · rcases Finset.mem_union.mp he with he | he
      · obtain ⟨hu, hv, hadj, hlen⟩ := mem_inducedEdges_cut.mp he
        exact mem_inducedEdges_cut.mpr ⟨(mem_rootComponentFinset.mp hu).1,
          (mem_rootComponentFinset.mp hv).1, hadj, hlen⟩
      · obtain ⟨hu, hv, hadj, hlen⟩ := mem_inducedEdges_cut.mp he
        exact mem_inducedEdges_cut.mpr ⟨(mem_rootComplementFinset.mp hu).1,
          (mem_rootComplementFinset.mp hv).1, hadj, hlen⟩

theorem inducedEdges_rootComponent_disjoint {d : ℕ} (D : Finset (TreeVertex d))
    (c : Fin d) : Disjoint (inducedEdges (rootComponentFinset D c))
      (inducedEdges (rootComplementFinset D c)) := by
  classical
  apply Finset.disjoint_left.mpr
  rintro ⟨u, v⟩ hu hv
  exact (mem_rootComplementFinset.mp (mem_inducedEdges_cut.mp hv).1).2
    (mem_rootComponentFinset.mp (mem_inducedEdges_cut.mp hu).1).2

theorem root_bridge_not_mem_inducedEdges_cut {d : ℕ} (D : Finset (TreeVertex d))
    (c : Fin d) : (ConnectedHull.root d, (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d)) ∉
      inducedEdges (rootComponentFinset D c) ∪ inducedEdges (rootComplementFinset D c) := by
  classical
  intro he
  rcases Finset.mem_union.mp he with he | he
  · have h := (mem_rootComponentFinset.mp (mem_inducedEdges_cut.mp he).1).2.length_le
    change 1 ≤ 0 at h
    omega
  · exact (mem_rootComplementFinset.mp (mem_inducedEdges_cut.mp he).2.1).2
      (List.prefix_refl _)

end Problem367

end

end OAI

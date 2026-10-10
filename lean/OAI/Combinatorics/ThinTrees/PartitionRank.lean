import OAI.Combinatorics.ThinTrees.BasePacking

namespace OAI

universe uE uI uV uE2 uV2

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

def internal (F : Finset (Fin m)) (A : Finset (Fin n)) : Finset (Fin m) :=
  F.filter (fun e => G.left e ∈ A ∧ G.right e ∈ A)

def ConnectedOn (A : Finset (Fin n)) (F : Finset (Fin m)) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, G.Same F u v

def TreeOn (A : Finset (Fin n)) (F : Finset (Fin m)) : Prop :=
  F ⊆ G.internal univ A ∧ G.ConnectedOn A F ∧ LinearIndepOn ℝ G.incidence (F : Set (Fin m))

def PackableOn (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) : Prop :=
  ∃ T : Fin q → Finset (Fin m),
    (∀ i, T i ⊆ G.internal F A ∧ G.ConnectedOn A (T i)) ∧
    ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j)

lemma connectedOn_mono_span {A : Finset (Fin n)} {F T : Finset (Fin m)}
    (h : G.edgeSpan F ≤ G.edgeSpan T) (hc : G.ConnectedOn A F) : G.ConnectedOn A T := by
  intro u hu v hv
  exact h (hc u hu v hv)

lemma connectedOn_mono {A : Finset (Fin n)} {F T : Finset (Fin m)}
    (h : F ⊆ T) (hc : G.ConnectedOn A F) : G.ConnectedOn A T :=
  G.connectedOn_mono_span (Packing.span_mono G.incidence h) hc

lemma independent_spanning_subset (F : Finset (Fin m)) :
    ∃ T ⊆ F, LinearIndepOn ℝ G.incidence (T : Set (Fin m)) ∧ G.edgeSpan T = G.edgeSpan F := by
  classical
  let h : LinearIndepOn ℝ G.incidence (∅ : Set (Fin m)) := linearIndepOn_empty ℝ G.incidence
  let U := h.extend (Set.empty_subset (F : Set (Fin m)))
  refine ⟨U.toFinset, ?_, ?_, ?_⟩
  · intro e he
    exact h.extend_subset (Set.empty_subset (F : Set (Fin m))) (Set.mem_toFinset.mp he)
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.empty_subset (F : Set (Fin m)))
  · simpa only [edgeSpan, Packing.span, Set.coe_toFinset] using
      h.span_image_extend_eq_span_image (Set.empty_subset (F : Set (Fin m)))

lemma packableOn_iff_trees (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) :
    G.PackableOn F q A ↔ ∃ T : Fin q → Finset (Fin m),
      (∀ i, T i ⊆ F ∧ G.TreeOn A (T i)) ∧
      ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j) := by
  classical
  constructor
  · rintro ⟨T, hT, hd⟩
    choose U hU hi hs using fun i => G.independent_spanning_subset (T i)
    refine ⟨U, fun i => ⟨?_, ?_, ?_, hi i⟩, fun i j hij =>
      disjoint_of_subset_left (hU i) (disjoint_of_subset_right (hU j) (hd hij))⟩
    · exact (hU i).trans ((hT i).1.trans (filter_subset _ _))
    · intro e he
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((hT i).1 (hU i he))).2⟩
    · exact G.connectedOn_mono_span (le_of_eq (hs i).symm) (hT i).2
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨?_, (hT i).2.2.1⟩, hd⟩
    intro e he
    exact mem_filter.mpr ⟨(hT i).1 he, (mem_filter.mp ((hT i).2.1 he)).2⟩

lemma packableOn_singleton (F : Finset (Fin m)) (q : ℕ) (u : Fin n) :
    G.PackableOn F q {u} := by
  refine ⟨fun _ => ∅, fun i => ⟨empty_subset _, ?_⟩, fun _ _ _ => disjoint_empty_left _⟩
  intro v hv w hw
  simp only [mem_singleton] at hv hw
  subst v; subst w
  exact G.same_refl _ _

lemma packableOn_mono_edges {F F' : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (h : F ⊆ F') (hp : G.PackableOn F q A) : G.PackableOn F' q A := by
  obtain ⟨T, hT, hd⟩ := hp
  exact ⟨T, fun i => ⟨(hT i).1.trans (filter_subset_filter _ h), (hT i).2⟩, hd⟩

lemma splice_span {A : Finset (Fin n)} {T U : Finset (Fin m)}
    (hT : G.ConnectedOn A T) : G.edgeSpan U ≤ G.edgeSpan (T ∪ (U \ G.internal univ A)) := by
  apply (Packing.span_le_iff G.incidence).mpr
  intro e he
  by_cases ha : e ∈ G.internal univ A
  · have heA := (mem_filter.mp ha).2
    exact Packing.span_mono G.incidence subset_union_left (hT _ heA.1 _ heA.2)
  · exact Packing.mem_span_self G.incidence (mem_union_right _ (mem_sdiff.mpr ⟨he, ha⟩))

theorem packableOn_union {F : Finset (Fin m)} {q : ℕ} {A B : Finset (Fin n)}
    (hA : G.PackableOn F q A) (hB : G.PackableOn F q B) (hAB : (A ∩ B).Nonempty) :
    G.PackableOn F q (A ∪ B) := by
  classical
  obtain ⟨T, hT, hdT⟩ := hA
  obtain ⟨U, hU, hdU⟩ := hB
  obtain ⟨w, hw⟩ := hAB
  obtain ⟨hwA, hwB⟩ := mem_inter.mp hw
  let W := fun i => T i ∪ (U i \ G.internal univ A)
  have hconn (i : Fin q) : G.ConnectedOn (A ∪ B) (W i) := by
    have h1 : G.ConnectedOn A (W i) := G.connectedOn_mono subset_union_left (hT i).2
    have h2 : G.ConnectedOn B (W i) := G.connectedOn_mono_span (G.splice_span (hT i).2) (hU i).2
    have hs : ∀ v ∈ A ∪ B, G.Same (W i) v w := by
      intro v hv
      rcases mem_union.mp hv with hv | hv
      · exact h1 v hv w hwA
      · exact h2 v hv w hwB
    intro u hu v hv
    exact G.same_trans (hs u hu) (G.same_symm (hs v hv))
  refine ⟨W, fun i => ⟨?_, hconn i⟩, ?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨heF, hl, hr⟩ := mem_filter.mp ((hT i).1 he)
      exact mem_filter.mpr ⟨heF, mem_union_left _ hl, mem_union_left _ hr⟩
    · obtain ⟨heF, hl, hr⟩ := mem_filter.mp ((hU i).1 (mem_sdiff.mp he).1)
      exact mem_filter.mpr ⟨heF, mem_union_right _ hl, mem_union_right _ hr⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro e he hi
    rcases mem_union.mp he with he | he <;> rcases mem_union.mp hi with hi | hi
    · exact disjoint_left.mp (hdT hij) he hi
    · exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((hT i).1 he)).2⟩)
    · exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((hT j).1 hi)).2⟩)
    · exact disjoint_left.mp (hdU hij) (mem_sdiff.mp he).1 (mem_sdiff.mp hi).1

def MaxPackable (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ G.PackableOn F q A ∧
    ∀ B, A ⊆ B → G.PackableOn F q B → B = A

def packingParts (F : Finset (Fin m)) (q : ℕ) : Finset (Finset (Fin n)) :=
  by classical exact univ.filter (G.MaxPackable F q)

lemma exists_maxPackable {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hA : A.Nonempty) (hp : G.PackableOn F q A) :
    ∃ B, A ⊆ B ∧ G.MaxPackable F q B := by
  classical
  let C : Finset (Finset (Fin n)) := univ.filter (fun B => A ⊆ B ∧ G.PackableOn F q B)
  have hC : A ∈ C := by simp [C, hp]
  obtain ⟨B, hB, hmax⟩ := exists_max_image C card ⟨A, hC⟩
  obtain ⟨hAB, hpB⟩ := (mem_filter.mp hB).2
  refine ⟨B, hAB, hA.mono hAB, hpB, ?_⟩
  intro D hBD hpD
  have hD : D ∈ C := mem_filter.mpr ⟨mem_univ _, hAB.trans hBD, hpD⟩
  exact (eq_of_subset_of_card_le hBD (hmax D hD)).symm

lemma maxPackable_disjoint {F : Finset (Fin m)} {q : ℕ} {A B : Finset (Fin n)}
    (hA : G.MaxPackable F q A) (hB : G.MaxPackable F q B) : A = B ∨ Disjoint A B := by
  classical
  by_cases h : Disjoint A B
  · exact Or.inr h
  · have hne : (A ∩ B).Nonempty := not_disjoint_iff_nonempty_inter.mp h
    have hp := G.packableOn_union hA.2.1 hB.2.1 hne
    exact Or.inl ((hA.2.2 _ subset_union_left hp).symm.trans (hB.2.2 _ subset_union_right hp))

lemma maxPackable_contains {F : Finset (Fin m)} {q : ℕ} {A B : Finset (Fin n)}
    (hA : G.MaxPackable F q A) (hB : G.PackableOn F q B) (hAB : (A ∩ B).Nonempty) : B ⊆ A := by
  have heq := hA.2.2 _ subset_union_left (G.packableOn_union hA.2.1 hB hAB)
  exact heq ▸ subset_union_right

theorem packingParts_partition (F : Finset (Fin m)) (q : ℕ) :
    (∀ A ∈ G.packingParts F q, A.Nonempty ∧ G.PackableOn F q A) ∧
    ((G.packingParts F q : Finset (Finset (Fin n))) : Set (Finset (Fin n))).Pairwise Disjoint ∧
    (G.packingParts F q).biUnion id = univ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    exact ⟨(mem_filter.mp hA).2.1, (mem_filter.mp hA).2.2.1⟩
  · intro A hA B hB hne
    exact (G.maxPackable_disjoint (mem_filter.mp hA).2 (mem_filter.mp hB).2).resolve_left hne
  · apply eq_univ_of_forall
    intro v
    obtain ⟨B, hvB, hB⟩ := G.exists_maxPackable (singleton_nonempty v) (G.packableOn_singleton F q v)
    exact mem_biUnion.mpr ⟨B, mem_filter.mpr ⟨mem_univ _, hB⟩, hvB (mem_singleton_self v)⟩

theorem packingParts_coarsens {F F' : Finset (Fin m)} {q : ℕ} (h : F ⊆ F') :
    ∀ A ∈ G.packingParts F q, ∃ B ∈ G.packingParts F' q, A ⊆ B := by
  classical
  intro A hA
  obtain ⟨hne, hp, hmax⟩ := (mem_filter.mp hA).2
  obtain ⟨B, hAB, hB⟩ := G.exists_maxPackable hne (G.packableOn_mono_edges h hp)
  exact ⟨B, mem_filter.mpr ⟨mem_univ _, hB⟩, hAB⟩

lemma connectedOn_univ (T : Finset (Fin m)) : G.ConnectedOn univ T ↔ G.Connected T := by
  rw [G.connected_iff_same]
  simp only [ConnectedOn, mem_univ, forall_const]

lemma packableOn_univ (F : Finset (Fin m)) (q : ℕ) :
    G.PackableOn F q univ ↔ G.TreePackable F q := by
  rw [G.packableOn_iff_trees]
  constructor
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_⟩, hd⟩
    exact (G.spanningTree_iff_independent _).mpr
      ⟨(G.connectedOn_univ _).mp (hT i).2.2.1, (hT i).2.2.2⟩
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_, ?_, ?_⟩, hd⟩
    · simp [internal]
    · exact (G.connectedOn_univ _).mpr (hT i).2.1
    · exact ((G.spanningTree_iff_independent _).mp (hT i).2).2

def vertexProjection (A : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x v := if v ∈ A then x v else 0
  map_add' x y := by ext v; by_cases hv : v ∈ A <;> simp [hv]
  map_smul' c x := by ext v; by_cases hv : v ∈ A <;> simp [hv]

lemma vertexProjection_point (A : Finset (Fin n)) (u : Fin n) :
    vertexProjection A (point u) = if u ∈ A then point u else 0 := by
  ext v
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> by_cases h : v = u <;>
    simp_all [vertexProjection, point]

lemma restrict_span {F : Finset (Fin m)} {A : Finset (Fin n)}
    (h : ∀ e ∈ F, G.left e ∈ A ↔ G.right e ∈ A) {x : Fin n → ℝ}
    (hx : x ∈ G.edgeSpan F) : vertexProjection A x ∈ G.edgeSpan (G.internal F A) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    have he' : e ∈ F := he
    rw [incidence, map_sub, vertexProjection_point, vertexProjection_point]
    by_cases hl : G.left e ∈ A
    · simp only [ite_eq_left hl, ite_eq_left ((h e he').mp hl)]
      exact Packing.mem_span_self G.incidence (mem_filter.mpr ⟨he', hl, (h e he').mp hl⟩)
    · simp [hl, not_congr (h e he') |>.mp hl]
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using smul_mem _ c ih

lemma restrict_same {F : Finset (Fin m)} {A : Finset (Fin n)}
    (h : ∀ e ∈ F, G.left e ∈ A ↔ G.right e ∈ A) {u v : Fin n}
    (hu : u ∈ A) (hv : v ∈ A) (hs : G.Same F u v) : G.Same (G.internal F A) u v := by
  have hp := G.restrict_span h hs
  change point u - point v ∈ G.edgeSpan (G.internal F A)
  simpa only [map_sub, vertexProjection_point, ite_eq_left hu, ite_eq_left hv] using hp

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.Packing
noncomputable section
open Finset Submodule
variable {E : Type uE} {I : Type uI} {V : Type uV} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in

theorem packing_certificate_on (v : E → V) (T : Finset E) :
    ∃ (F : I → Finset E) (U : Finset E), Valid v F ∧
      (∀ i, F i ⊆ T) ∧ U ⊆ T ∧
      (∀ i, span v U = span v (F i ∩ U)) ∧
      (∑ i, (F i).card) = (T \ U).card + Fintype.card I * Module.finrank ℝ (span v U) := by
  classical
  let w : E → V := fun e => if e ∈ T then v e else 0
  obtain ⟨F, hF⟩ := exists_maximal_state (I := I) w
  have hsub (i : I) : F.1 i ⊆ T := by
    intro e he
    have hz := (F.2.1 i).ne_zero he
    by_contra h
    exact hz (by simp [w, h])
  let U := recycled F ∩ T
  have hout {e : E} (he : e ∉ T) : e ∈ recycled F := by
    apply mem_recycled.mpr
    refine ⟨F, Relation.ReflTransGen.refl, ?_⟩
    intro i hi
    exact he (hsub i hi)
  have hdiff : univ \ recycled F = T \ U := by
    ext e
    simp only [mem_sdiff, mem_univ, true_and, U, mem_inter]
    constructor
    · intro h; exact ⟨by_contra (fun he => h (hout he)), fun he => h he.1⟩
    · rintro ⟨hT, h⟩ hr; exact h ⟨hr, hT⟩
  refine ⟨F.1, U, ⟨?_, F.2.2⟩, hsub, inter_subset_right, ?_, ?_⟩
  · intro i
    apply (F.2.1 i).congr
    intro e he; simp [w, hsub i he]
  · intro i
    have hs := span_recycled_eq hF i
    change span v (recycled F ∩ T) = span v (F.1 i ∩ (recycled F ∩ T))
    rw [← inter_assoc]
    simpa only [w, masked_span] using hs
  · have hc := cost_decomposition hF
    rw [hdiff] at hc
    change cost F = (T \ U).card + Fintype.card I *
      Module.finrank ℝ (span (fun e => if e ∈ T then v e else 0) (recycled F)) at hc
    rw [masked_span] at hc
    exact hc

end
end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

lemma component_packable_of_certificate {F U : Finset (Fin m)} {q : ℕ}
    {T : Fin q → Finset (Fin m)} (hT : ∀ i, T i ⊆ F)
    (hd : ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j))
    (hs : ∀ i, G.edgeSpan U = G.edgeSpan (T i ∩ U)) (v : Fin n) :
    G.PackableOn F q (univ.filter (fun w => G.rep U w = G.rep U v)) := by
  let A := univ.filter (fun w => G.rep U w = G.rep U v)
  refine ⟨fun i => G.internal (T i ∩ U) A, fun i => ⟨?_, ?_⟩, ?_⟩
  · exact filter_subset_filter _ (inter_subset_left.trans (hT i))
  · intro u hu w hw
    have hu' : G.rep U u = G.rep U v := (mem_filter.mp hu).2
    have hw' : G.rep U w = G.rep U v := (mem_filter.mp hw).2
    have hh : G.Same (T i ∩ U) u w := by
      rw [Same, ← hs i]
      exact (G.rep_eq_iff U u w).mp (hu'.trans hw'.symm)
    refine G.restrict_same ?_ hu hw hh
    intro e he
    simp only [A, mem_filter, mem_univ, true_and, G.rep_endpoints (mem_inter.mp he).2]
  · intro i j hij
    exact disjoint_of_subset_left (filter_subset _ _ |>.trans inter_subset_left)
      (disjoint_of_subset_right (filter_subset _ _ |>.trans inter_subset_left) (hd hij))

def partOf (F : Finset (Fin m)) (q : ℕ) (v : Fin n) : Finset (Fin n) :=
  Classical.choose (G.exists_maxPackable (singleton_nonempty v) (G.packableOn_singleton F q v))

lemma partOf_spec (F : Finset (Fin m)) (q : ℕ) (v : Fin n) :
    v ∈ G.partOf F q v ∧ G.MaxPackable F q (G.partOf F q v) := by
  have h := Classical.choose_spec (G.exists_maxPackable (singleton_nonempty v) (G.packableOn_singleton F q v))
  exact ⟨h.1 (mem_singleton_self _), h.2⟩

lemma partOf_eq_iff (F : Finset (Fin m)) (q : ℕ) (u v : Fin n) :
    G.partOf F q u = G.partOf F q v ↔ u ∈ G.partOf F q v := by
  constructor
  · intro h; rw [← h]; exact (G.partOf_spec F q u).1
  · intro h
    rcases G.maxPackable_disjoint (G.partOf_spec F q u).2 (G.partOf_spec F q v).2 with heq | hd
    · exact heq
    · exact False.elim (disjoint_left.mp hd (G.partOf_spec F q u).1 h)

lemma partOf_eq_of_mem {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hA : G.MaxPackable F q A) {v : Fin n} (hv : v ∈ A) : G.partOf F q v = A := by
  rcases G.maxPackable_disjoint (G.partOf_spec F q v).2 hA with heq | hd
  · exact heq
  · exact False.elim (disjoint_left.mp hd (G.partOf_spec F q v).1 hv)

def partLabel (F : Finset (Fin m)) (q : ℕ) (v : Fin n) : Fin n :=
  (G.partOf F q v).min' (G.partOf_spec F q v).2.1

lemma partLabel_mem (F : Finset (Fin m)) (q : ℕ) (v : Fin n) :
    G.partLabel F q v ∈ G.partOf F q v := min'_mem _ _

lemma partLabel_eq_iff (F : Finset (Fin m)) (q : ℕ) (u v : Fin n) :
    G.partLabel F q u = G.partLabel F q v ↔ G.partOf F q u = G.partOf F q v := by
  constructor
  · intro h
    rcases G.maxPackable_disjoint (G.partOf_spec F q u).2 (G.partOf_spec F q v).2 with heq | hd
    · exact heq
    · exact False.elim (disjoint_left.mp hd (G.partLabel_mem F q u) (h ▸ G.partLabel_mem F q v))
  · intro h
    unfold partLabel
    congr 1

lemma partLabel_idempotent (F : Finset (Fin m)) (q : ℕ) (v : Fin n) :
    G.partLabel F q (G.partLabel F q v) = G.partLabel F q v := by
  apply (G.partLabel_eq_iff F q _ _).mpr
  exact (G.partOf_eq_iff F q _ _).mpr (G.partLabel_mem F q v)

lemma partLabel_size (F : Finset (Fin m)) (q : ℕ) :
    partitionSize (G.partLabel F q) = (G.packingParts F q).card := by
  classical
  apply card_bij (fun v _ => G.partOf F q v)
  · intro v hv
    exact mem_filter.mpr ⟨mem_univ _, (G.partOf_spec F q v).2⟩
  · intro u hu v hv heq
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hv
    have h := (G.partLabel_eq_iff F q _ _).mpr heq
    simpa only [G.partLabel_idempotent] using h
  · intro A hA
    have hm : G.MaxPackable F q A := (mem_filter.mp hA).2
    obtain ⟨v, hv⟩ := hm.1
    refine ⟨G.partLabel F q v, mem_image.mpr ⟨v, mem_univ _, rfl⟩, ?_⟩
    have heq := G.partOf_eq_of_mem hm hv
    exact (G.partOf_eq_iff F q _ _).mpr (G.partLabel_mem F q v) |>.trans heq

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.Packing
noncomputable section
open Finset Submodule
variable {E : Type uE2} {V : Type uV2} [Fintype E] [DecidableEq E]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_rank_le_card (v : E → V) (T : Finset E) :
    Module.finrank ℝ (span v T) ≤ T.card := by
  classical
  have h := finrank_span_finset_le_card (R := ℝ) (T.image v)
  rw [coe_image] at h
  exact h.trans card_image_le

omit [Fintype E] in
lemma rank_le_sdiff_card_add (v : E → V) (T U : Finset E) :
    Module.finrank ℝ (span v T) ≤ (T \ U).card + Module.finrank ℝ (span v U) := by
  have hsub : span v T ≤ span v (T \ U) ⊔ span v U := by
    apply (span_le_iff v).mpr
    intro e he
    by_cases h : e ∈ U
    · exact (show span v U ≤ span v (T \ U) ⊔ span v U from le_sup_right) (mem_span_self v h)
    · exact (show span v (T \ U) ≤ span v (T \ U) ⊔ span v U from le_sup_left) (mem_span_self v (mem_sdiff.mpr ⟨he, h⟩))
  exact (Submodule.finrank_mono hsub).trans
    ((show Module.finrank ℝ (span v (T \ U) ⊔ span v U : Submodule ℝ V) ≤
        Module.finrank ℝ (span v (T \ U)) + Module.finrank ℝ (span v U) by
        have h := Submodule.finrank_sup_add_finrank_inf_eq (span v (T \ U)) (span v U)
        omega).trans (Nat.add_le_add_right (span_rank_le_card v _) _))

end
end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

def withinParts (F : Finset (Fin m)) (q : ℕ) : Finset (Fin m) :=
  F.filter (fun e => G.partLabel F q (G.left e) = G.partLabel F q (G.right e))

lemma internal_subset_withinParts {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hA : G.MaxPackable F q A) : G.internal F A ⊆ G.withinParts F q := by
  intro e he
  obtain ⟨heF, hl, hr⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨heF, (G.partLabel_eq_iff F q _ _).mpr
    ((G.partOf_eq_of_mem hA hl).trans (G.partOf_eq_of_mem hA hr).symm)⟩

lemma same_withinParts {F : Finset (Fin m)} {q : ℕ} (hq : 0 < q) (u v : Fin n) :
    G.Same (G.withinParts F q) u v ↔ G.partLabel F q u = G.partLabel F q v := by
  constructor
  · exact G.same_preserves_label (fun e he => (mem_filter.mp he).2)
  · intro h
    let A := G.partOf F q u
    have hA : G.MaxPackable F q A := (G.partOf_spec F q u).2
    have hu : u ∈ A := (G.partOf_spec F q u).1
    have hv : v ∈ A := by
      change v ∈ G.partOf F q u
      rw [(G.partLabel_eq_iff F q u v).mp h]
      exact (G.partOf_spec F q v).1
    obtain ⟨T, hT, hd⟩ := hA.2.1
    let i : Fin q := ⟨0, hq⟩
    exact Packing.span_mono G.incidence
      ((hT i).1.trans (G.internal_subset_withinParts hA)) ((hT i).2 u hu v hv)

lemma componentCount_eq_partitionSize {T : Finset (Fin m)} {p : Fin n → Fin n}
    (h : ∀ u v, G.Same T u v ↔ p u = p v) : G.componentCount T = partitionSize p := by
  classical
  apply card_bij (fun v _ => p v)
  · intro v hv; exact mem_image.mpr ⟨v, mem_univ _, rfl⟩
  · intro u hu v hv hp
    have hr := (G.rep_eq_iff T u v).mpr ((h u v).mpr hp)
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hv
    simpa only [G.rep_idempotent] using hr
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hc
    exact ⟨G.rep T v, mem_image.mpr ⟨v, mem_univ _, rfl⟩,
      (h _ _).mp (G.rep_same T v)⟩

lemma withinParts_rank {F : Finset (Fin m)} {q : ℕ} (hq : 0 < q) :
    Module.finrank ℝ (G.edgeSpan (G.withinParts F q)) =
      n - (G.packingParts F q).card := by
  rw [G.incidence_rank, G.componentCount_eq_partitionSize (G.same_withinParts hq), G.partLabel_size]

lemma withinParts_spanning_packing (F : Finset (Fin m)) (q : ℕ) :
    ∃ S : Fin q → Finset (Fin m),
      (∀ i, S i ⊆ G.withinParts F q ∧ G.edgeSpan (S i) = G.edgeSpan (G.withinParts F q)) ∧
      ∀ ⦃i j⦄, i ≠ j → Disjoint (S i) (S j) := by
  classical
  let P := G.packingParts F q
  have hp (A : ↥P) : G.PackableOn F q A.val := (mem_filter.mp A.property).2.2.1
  choose T hT hd using hp
  let S := fun i => univ.biUnion (fun A : ↥P => T A i)
  have hmax (A : ↥P) : G.MaxPackable F q A.val := (mem_filter.mp A.property).2
  have hsub (i : Fin q) : S i ⊆ G.withinParts F q := by
    apply biUnion_subset.mpr
    intro A hA
    exact (hT A i).1.trans (G.internal_subset_withinParts (hmax A))
  refine ⟨S, fun i => ⟨hsub i, ?_⟩, ?_⟩
  · apply le_antisymm (Packing.span_mono G.incidence (hsub i))
    apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have heq := (G.partLabel_eq_iff F q _ _).mp (mem_filter.mp he).2
    let A : ↥P := ⟨G.partOf F q (G.left e), mem_filter.mpr ⟨mem_univ _, (G.partOf_spec F q _).2⟩⟩
    have hl : G.left e ∈ A.val := (G.partOf_spec F q _).1
    have hr : G.right e ∈ A.val := by
      change G.right e ∈ G.partOf F q (G.left e)
      rw [heq]
      exact (G.partOf_spec F q _).1
    exact Packing.span_mono G.incidence (subset_biUnion_of_mem (fun A : ↥P => T A i) (mem_univ A))
      ((hT A i).2 _ hl _ hr)
  · intro i j hij
    apply disjoint_left.mpr
    intro e he hi
    obtain ⟨A, hA, heA⟩ := mem_biUnion.mp he
    obtain ⟨B, hB, heB⟩ := mem_biUnion.mp hi
    have hlA := (mem_filter.mp ((hT A i).1 heA)).2.1
    have hlB := (mem_filter.mp ((hT B j).1 heB)).2.1
    have hab : A = B := by
      apply Subtype.ext
      rcases G.maxPackable_disjoint (hmax A) (hmax B) with heq | hd
      · exact heq
      · exact False.elim (disjoint_left.mp hd hlA hlB)
    subst B
    exact disjoint_left.mp (hd A hij) heA heB

lemma recycled_subset_withinParts {F U : Finset (Fin m)} {q : ℕ}
    {T : Fin q → Finset (Fin m)} (hT : ∀ i, T i ⊆ F) (hUF : U ⊆ F)
    (hd : ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j))
    (hs : ∀ i, G.edgeSpan U = G.edgeSpan (T i ∩ U)) : U ⊆ G.withinParts F q := by
  intro e he
  let A := G.partOf F q (G.left e)
  let B := univ.filter (fun w => G.rep U w = G.rep U (G.left e))
  have hpB : G.PackableOn F q B := G.component_packable_of_certificate hT hd hs (G.left e)
  have hsub := G.maxPackable_contains (G.partOf_spec F q (G.left e)).2 hpB
    (show (A ∩ B).Nonempty from ⟨G.left e, mem_inter.mpr ⟨(G.partOf_spec F q _).1, by simp [B]⟩⟩)
  have hr : G.right e ∈ A := hsub (by simp only [B, mem_filter, mem_univ, true_and]; exact (G.rep_endpoints he).symm)
  have hlabel := (G.partLabel_eq_iff F q (G.right e) (G.left e)).mpr ((G.partOf_eq_iff F q _ _).mpr hr)
  exact mem_filter.mpr ⟨hUF he, hlabel.symm⟩

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

lemma not_packable_of_parts {F : Finset (Fin m)} {q : ℕ}
    (hparts : 1 < (G.packingParts F q).card) : ¬G.TreePackable F q := by
  classical
  intro hp
  have hull := (G.packableOn_univ F q).mpr hp
  have hsub : G.packingParts F q ⊆ {univ} := by
    intro A hA
    have hm : G.MaxPackable F q A := (mem_filter.mp hA).2
    exact mem_singleton.mpr (hm.2.2 _ (subset_univ _) hull).symm
  have hc := card_le_card hsub
  simp only [card_singleton] at hc
  omega

lemma forest_card_le {T : Finset (Fin m)} (hn : 0 < n)
    (hi : LinearIndepOn ℝ G.incidence (T : Set (Fin m))) : T.card ≤ n - 1 := by
  have hr := Packing.indep_rank G.incidence hi
  change Module.finrank ℝ (G.edgeSpan T) = T.card at hr
  rw [G.incidence_rank] at hr
  have hp := G.componentCount_pos hn T
  omega

lemma packing_cost_lt {F : Finset (Fin m)} {q : ℕ} (hn : 0 < n)
    (hp : ¬G.TreePackable F q) {T : Fin q → Finset (Fin m)}
    (hv : Packing.Valid G.incidence T) (hs : ∀ i, T i ⊆ F) :
    (∑ i, (T i).card) < q * (n - 1) := by
  classical
  have hle (i : Fin q) : (T i).card ≤ n - 1 := G.forest_card_le hn (hv.1 i)
  have ht : (∑ i, (T i).card) ≤ q * (n - 1) := by
    calc
      _ ≤ ∑ _i : Fin q, (n - 1) := sum_le_sum (fun i _ => hle i)
      _ = _ := by simp
  by_contra h
  have heq : (∑ i, (T i).card) = ∑ _i : Fin q, (n - 1) := by simpa using (Nat.le_antisymm ht (by omega))
  have hi := (sum_eq_sum_iff_of_le (fun i (_ : i ∈ (univ : Finset (Fin q))) => hle i)).mp heq
  apply hp
  refine ⟨T, fun i => ⟨hs i, (G.spanningTree_iff_independent _).mpr ⟨?_, hv.1 i⟩⟩, hv.2⟩
  apply G.connected_of_componentCount_eq_one
  have hc := hi i (mem_univ i)
  have hr := Packing.indep_rank G.incidence (hv.1 i)
  change Module.finrank ℝ (G.edgeSpan (T i)) = (T i).card at hr
  rw [G.incidence_rank, hc] at hr
  have hp := G.componentCount_pos hn (T i)
  have hnz : 0 < n := hn
  have hcn := G.componentCount_le (T i)
  omega

lemma withinParts_rank_count {F U : Finset (Fin m)} {q : ℕ} :
    q * Module.finrank ℝ (G.edgeSpan (G.withinParts F q)) ≤
      (G.withinParts F q \ U).card + q * Module.finrank ℝ (G.edgeSpan U) := by
  classical
  obtain ⟨S, hS, hd⟩ := G.withinParts_spanning_packing F q
  have hi (i : Fin q) : Module.finrank ℝ (G.edgeSpan (G.withinParts F q)) ≤
      (S i \ U).card + Module.finrank ℝ (G.edgeSpan U) := by
    rw [← (hS i).2]
    exact Packing.rank_le_sdiff_card_add G.incidence (S i) U
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin q))) => hi i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hcard : (∑ i, (S i \ U).card) ≤ (G.withinParts F q \ U).card := by
    rw [← card_biUnion]
    · apply card_le_card
      intro e he
      obtain ⟨i, hi, he⟩ := mem_biUnion.mp he
      exact mem_sdiff.mpr ⟨(hS i).1 (mem_sdiff.mp he).1, (mem_sdiff.mp he).2⟩
    · intro i hi j hj hij
      exact disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right sdiff_subset (hd hij))
  exact hsum.trans (Nat.add_le_add_right hcard _)

theorem packingParts_crossing_lt {F : Finset (Fin m)} {q : ℕ} (hq : 0 < q)
    (hparts : 1 < (G.packingParts F q).card) :
    (G.crossing F (G.partLabel F q)).card < q * ((G.packingParts F q).card - 1) := by
  classical
  have hn : 0 < n := by
    have hsz := G.partLabel_size F q
    have hc : partitionSize (G.partLabel F q) ≤ n :=
      card_image_le.trans_eq (card_univ.trans (Fintype.card_fin n))
    omega
  obtain ⟨T, U, hv, hs, hUF, heq, hcost⟩ :=
    Packing.packing_certificate_on (I := Fin q) G.incidence F
  simp only [Fintype.card_fin] at hcost
  have hlt := G.packing_cost_lt hn (G.not_packable_of_parts hparts) hv hs
  have hUJ := G.recycled_subset_withinParts hs hUF hv.2 heq
  have hJ := G.withinParts_rank_count (F := F) (U := U) (q := q)
  rw [G.withinParts_rank hq] at hJ
  have hd : (G.withinParts F q \ U).card + (G.crossing F (G.partLabel F q)).card = (F \ U).card := by
    have hdis : Disjoint (G.withinParts F q \ U) (G.crossing F (G.partLabel F q)) := by
      apply disjoint_left.mpr
      intro e he hc
      exact (mem_filter.mp hc).2 (mem_filter.mp (mem_sdiff.mp he).1).2
    rw [← card_union_of_disjoint hdis]
    congr 1
    ext e
    simp only [mem_union, mem_sdiff, withinParts, crossing, mem_filter]
    constructor
    · rintro (⟨⟨heF, hp⟩, heU⟩ | ⟨heF, hp⟩)
      · exact ⟨heF, heU⟩
      · exact ⟨heF, fun heU => hp (mem_filter.mp (hUJ heU)).2⟩
    · rintro ⟨heF, heU⟩
      by_cases hp : G.partLabel F q (G.left e) = G.partLabel F q (G.right e)
      · exact Or.inl ⟨⟨heF, hp⟩, heU⟩
      · exact Or.inr ⟨heF, hp⟩
  have hsz : (G.packingParts F q).card ≤ n := by
    rw [← G.partLabel_size F q]
    exact card_image_le.trans_eq (card_univ.trans (Fintype.card_fin n))
  have hid : n - 1 = (n - (G.packingParts F q).card) + ((G.packingParts F q).card - 1) := by omega
  rw [hid, Nat.mul_add, hcost, ← hd] at hlt
  change q * (n - (G.packingParts F q).card) ≤ _ + q * Module.finrank ℝ (Packing.span G.incidence U) at hJ
  omega

end
end StrongThinTree.MultiGraph

end

end OAI

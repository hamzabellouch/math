import OAI.Analysis.ProductSpaces.ConditionalBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uκ

namespace IndependentProducts
/-- Finite predecessor-closed heads, including the root. -/
structure FiniteHead where
  vertices : Finset Vertex
  root_mem : [] ∈ vertices
  prefix_mem : ∀ {u v : Vertex}, u <+: v → v ∈ vertices → u ∈ vertices

namespace FiniteHead
variable (T : FiniteHead)

/-- First-exit vertices. -/
def Boundary := {e : Edge // e.val ∉ T.vertices ∧ e.val.dropLast ∈ T.vertices}

lemma boundary_eq_of_prefix {e f : T.Boundary} (h : e.val.val <+: f.val.val) : e = f := by
  apply Subtype.ext
  apply Subtype.ext
  by_contra hne
  have hlen : e.val.val.length < f.val.val.length := by
    have hle := h.length_le
    have hn : e.val.val.length ≠ f.val.val.length := fun he => hne (h.eq_of_length he)
    omega
  have hp : e.val.val <+: f.val.val.dropLast := by
    rw [List.dropLast_eq_take]
    exact List.prefix_take_iff.mpr ⟨h, by omega⟩
  exact e.property.1 (T.prefix_mem hp f.property.2)

lemma boundary_unique {v : Vertex} {e f : T.Boundary}
    (he : e.val.val <+: v) (hf : f.val.val <+: v) : e = f := by
  rcases List.prefix_or_prefix_of_prefix he hf with h | h
  · exact T.boundary_eq_of_prefix h
  · exact (T.boundary_eq_of_prefix h).symm

lemma exists_boundary_prefix (v : Vertex) (hv : v ∉ T.vertices) :
    ∃ e : T.Boundary, e.val.val <+: v := by
  induction v using List.reverseRecOn with
  | nil => exact (hv T.root_mem).elim
  | append_singleton v a ih =>
    by_cases h : v ∈ T.vertices
    · refine ⟨⟨⟨v ++ [a], by simp⟩, hv, ?_⟩, List.prefix_rfl⟩
      simpa using h
    · obtain ⟨e, he⟩ := ih h
      exact ⟨e, List.prefix_append_of_prefix he⟩

noncomputable def exit (v : Vertex) (hv : v ∉ T.vertices) : T.Boundary :=
  Classical.choose (T.exists_boundary_prefix v hv)

lemma exit_prefix (v : Vertex) (hv : v ∉ T.vertices) : (T.exit v hv).val.val <+: v :=
  Classical.choose_spec (T.exists_boundary_prefix v hv)

lemma exit_eq (v : Vertex) (hv : v ∉ T.vertices) (e : T.Boundary)
    (he : e.val.val <+: v) : T.exit v hv = e := T.boundary_unique (T.exit_prefix v hv) he

/-- The last head ancestor of any vertex. -/
noncomputable def ancestor (v : Vertex) : Vertex :=
  if h : v ∈ T.vertices then v else (T.exit v h).val.val.dropLast

lemma ancestor_mem (v : Vertex) : T.ancestor v ∈ T.vertices := by
  unfold ancestor
  split_ifs with h
  · exact h
  · exact (T.exit v h).property.2

lemma ancestor_prefix (v : Vertex) : T.ancestor v <+: v := by
  unfold ancestor
  split_ifs with h
  · exact List.prefix_rfl
  · exact (List.dropLast_prefix _).trans (T.exit_prefix v h)

@[simp] lemma ancestor_of_mem {v : Vertex} (hv : v ∈ T.vertices) : T.ancestor v = v := by
  simp [ancestor, hv]

lemma ancestor_of_not_mem {v : Vertex} (hv : v ∉ T.vertices) :
    T.ancestor v = (T.exit v hv).val.val.dropLast := by simp [ancestor, hv]

lemma no_boundary_prefix_head {v : Vertex} (hv : v ∈ T.vertices) (e : T.Boundary) :
    ¬ e.val.val <+: v := fun h => e.property.1 (T.prefix_mem h hv)

/-- A head containing any given finite list of vertices. -/
def containing (s : Finset Vertex) : FiniteHead where
  vertices := {[]} ∪ s.biUnion (fun v => (Finset.range (v.length + 1)).image (fun n => v.take n))
  root_mem := by simp
  prefix_mem := by
    intro u v huv hv
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_range] at hv ⊢
    rcases hv with rfl | ⟨w, hw, n, hn, rfl⟩
    · exact Or.inl (List.prefix_nil.mp huv)
    · right
      refine ⟨w, hw, u.length, ?_, ?_⟩
      · have hl := huv.length_le
        simp only [List.length_take] at hl
        omega
      · have hp : u <+: w := huv.trans (List.take_prefix _ _)
        exact (List.prefix_iff_eq_take.mp hp).symm

lemma mem_containing (s : Finset Vertex) {v : Vertex} (hv : v ∈ s) :
    v ∈ (containing s).vertices := by
  simp only [containing, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_range]
  exact Or.inr ⟨v, hv, v.length, by omega, List.take_length⟩

end FiniteHead
end IndependentProducts

namespace IndependentProducts

lemma mem_pathEdges_iff (v : Vertex) (e : Edge) : e ∈ pathEdges v ↔ e.val <+: v := by
  classical
  simp only [pathEdges, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, rfl⟩
    exact List.take_prefix _ _
  · intro h
    have hlen : 0 < e.val.length := List.length_pos_iff.mpr e.property
    refine ⟨⟨e.val.length - 1, by have := h.length_le; omega⟩, ?_⟩
    apply Subtype.ext
    change v.take (e.val.length - 1 + 1) = e.val
    rw [Nat.sub_add_cancel (by omega), ← List.prefix_iff_eq_take.mp h]

lemma pathEdges_mono {u v : Vertex} (h : u <+: v) : pathEdges u ⊆ pathEdges v := by
  intro e he
  exact (mem_pathEdges_iff v e).mpr (((mem_pathEdges_iff u e).mp he).trans h)

lemma self_mem_pathEdges (e : Edge) : e ∈ pathEdges e.val :=
  (mem_pathEdges_iff _ _).mpr List.prefix_rfl

lemma pathEdges_parent (e : Edge) : pathEdges e.val = insert e (pathEdges e.val.dropLast) := by
  classical
  ext f
  simp only [Finset.mem_insert, mem_pathEdges_iff]
  constructor
  · intro h
    by_cases he : f = e
    · exact Or.inl he
    · right
      rw [List.dropLast_eq_take]
      refine List.prefix_take_iff.mpr ⟨h, ?_⟩
      have hl := h.length_le
      have hn : f.val.length ≠ e.val.length := fun hp => he (Subtype.ext (h.eq_of_length hp))
      omega
  · rintro (rfl | h)
    · exact List.prefix_rfl
    · exact h.trans (List.dropLast_prefix _)

lemma self_not_mem_pathEdges_parent (e : Edge) : e ∉ pathEdges e.val.dropLast := by
  intro h
  have hh := ((mem_pathEdges_iff _ _).mp h).length_le
  have hp : 0 < e.val.length := List.length_pos_iff.mpr e.property
  simp only [List.length_dropLast] at hh
  omega

section Selector
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- Any coordinatewise choice from independent whole samples is again a product sample.
The second index is unchanged, so the selected scalar coordinates are all distinct. -/
lemma measurePreserving_sampleSelector {κ : Type uκ} [Fintype κ] (s : Edge → κ) :
    MeasurePreserving (fun ω : κ → Sample => fun e => ω (s e) e)
      (Measure.pi (fun _ : κ => productMeasure μ)) (productMeasure μ) := by
  have hi : iIndepFun (fun (p : (k : κ) × Edge) (ω : κ → Sample) => ω p.1 p.2)
      (Measure.pi (fun _ : κ => productMeasure μ)) := by
    have h := iIndepFun_uncurry_infinitePi
      (fun (_ : κ) (_ : Edge) => μ) (X := fun (_ : κ) (_ : Edge) (x : ℝ) => x)
      (by fun_prop)
    simpa only [Measure.infinitePi_eq_pi, productMeasure] using h
  have hinj : Function.Injective (fun e : Edge => (⟨s e, e⟩ : (k : κ) × Edge)) := by
    intro e f h
    exact congrArg Sigma.snd h
  have hsel := hi.precomp hinj
  refine ⟨by fun_prop, ?_⟩
  rw [hsel.map_fun_eq_infinitePi_map (by fun_prop)]
  unfold productMeasure
  congr 1
  funext e
  exact ((measurePreserving_eval_infinitePi (fun _ : Edge => μ) e).comp
    (measurePreserving_eval (fun _ : κ => productMeasure μ) (s e))).map_eq

end Selector
end IndependentProducts

end

end OAI

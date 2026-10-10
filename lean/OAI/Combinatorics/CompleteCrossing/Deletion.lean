import OAI.Combinatorics.CompleteCrossing.Drawing
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

namespace OAI

/-! Vertex deletion, its crossing-count identity, and small complete graphs. -/

section

/-! Source-faithful restriction of an actual complete-graph drawing by one vertex. -/
noncomputable section
namespace Paper170

structure VertexDeletion {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) (A : AdmissibleDrawing (completeGraph n)) : Prop where
  vertex_eq : ∀ i, A.vertex i = D.vertex (v.succAbove i)
  edge_eq : ∀ (e : CompleteEdge n) (f : CompleteEdge (n + 1)),
    f.val.1 = v.succAbove e.val.1 → f.val.2 = v.succAbove e.val.2 →
    ∀ t, A.edge e t = D.edge f t

end Paper170

end
end

section

noncomputable section
open scoped Classical
namespace Paper170

lemma crossingCount_zero_of_subsingleton {V E : Type} [Subsingleton E] {G : Graph V E}
    (D : AdmissibleDrawing G) : crossingCount D = 0 := by
  have h : crossingPoints D.toContinuousDrawing = ∅ := by
    ext x
    constructor
    · rintro ⟨e, f, hef, _, _⟩
      exact (hef (Subsingleton.elim e f)).elim
    · simp
  simp [crossingCount, h]

lemma ordinaryCrossingNumber_zero_of_subsingleton {V E : Type} [Subsingleton E]
    (G : Graph V E) : ordinaryCrossingNumber G = 0 := by
  by_cases h : (Set.range (@crossingCount V E G)).Nonempty
  · obtain ⟨_, D, rfl⟩ := h
    apply Nat.eq_zero_of_le_zero
    rw [← crossingCount_zero_of_subsingleton D]
    exact Paper170Geometry.ordinaryCrossingNumber_le_count D
  · simp [ordinaryCrossingNumber, Set.not_nonempty_iff_eq_empty.mp h]

theorem complete_graph_small_orders :
    ordinaryCrossingNumber (completeGraph 1) = 0 ∧
      ordinaryCrossingNumber (completeGraph 2) = 0 := by
  constructor
  · have : Subsingleton (CompleteEdge 1) := ⟨fun e f => by
      have := e.property
      have h1 := e.val.1.isLt
      have h2 := e.val.2.isLt
      omega⟩
    exact ordinaryCrossingNumber_zero_of_subsingleton _
  · have : Subsingleton (CompleteEdge 2) := ⟨fun e f => by
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      all_goals
        have he := e.property
        have hf := f.property
        have he1 := e.val.1.isLt
        have he2 := e.val.2.isLt
        have hf1 := f.val.1.isLt
        have hf2 := f.val.2.isLt
        omega⟩
    exact ordinaryCrossingNumber_zero_of_subsingleton _

end Paper170

end
end

section

noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170

def deletionEdge {n : ℕ} (v : Fin (n + 1)) (e : CompleteEdge n) : CompleteEdge (n + 1) :=
  ⟨(v.succAbove e.val.1, v.succAbove e.val.2), Fin.strictMono_succAbove v e.property⟩

lemma deletionEdge_injective {n : ℕ} (v : Fin (n + 1)) :
    Function.Injective (deletionEdge v) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.succAbove_right_injective (congrArg (fun a => a.val.1) h)
  · exact Fin.succAbove_right_injective (congrArg (fun a => a.val.2) h)

lemma deletionEdge_range {n : ℕ} (v : Fin (n + 1)) (e : CompleteEdge (n + 1)) :
    (∃ f, deletionEdge v f = e) ↔ e.val.1 ≠ v ∧ e.val.2 ≠ v := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨Fin.succAbove_ne v _, Fin.succAbove_ne v _⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h1
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq h2
    have hab : a < b := (Fin.strictMono_succAbove v).lt_iff_lt.mp (by
      rw [ha, hb]
      exact e.property)
    exact ⟨⟨(a,b), hab⟩, Subtype.ext (Prod.ext ha hb)⟩

def deleteContinuousDrawing {n : ℕ} (D : ContinuousDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : ContinuousDrawing (completeGraph n) where
  vertex i := D.vertex (v.succAbove i)
  vertex_injective := D.vertex_injective.comp Fin.succAbove_right_injective
  edge e := D.edge (deletionEdge v e)
  edge_injective e := D.edge_injective (deletionEdge v e)
  interior_avoids_vertices e t ht i :=
    D.interior_avoids_vertices (deletionEdge v e) t ht (v.succAbove i)

lemma deletion_crossings_subset {n : ℕ} (D : ContinuousDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : crossingPoints (deleteContinuousDrawing D v) ⊆ crossingPoints D := by
  rintro x ⟨e, f, hef, he, hf⟩
  exact ⟨deletionEdge v e, deletionEdge v f,
    fun h => hef (deletionEdge_injective v h), he, hf⟩

def deleteDrawing {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : AdmissibleDrawing (completeGraph n) where
  toContinuousDrawing := deleteContinuousDrawing D.toContinuousDrawing v
  crossings_finite := D.crossings_finite.subset (deletion_crossings_subset _ v)
  crossings_proper e f hef x he hf := D.crossings_proper (deletionEdge v e) (deletionEdge v f)
    (fun h => hef (deletionEdge_injective v h)) x he hf
  no_triples e f g hef heg hfg := D.no_triples (deletionEdge v e) (deletionEdge v f)
    (deletionEdge v g) (fun h => hef (deletionEdge_injective v h))
    (fun h => heg (deletionEdge_injective v h)) (fun h => hfg (deletionEdge_injective v h))

lemma deleteDrawing_spec {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : VertexDeletion D v (deleteDrawing D v) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro e f h1 h2 t
  have h : f = deletionEdge v e := Subtype.ext (Prod.ext h1 h2)
  subst f
  rfl

lemma deletion_crossing_iff {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) (x : Plane) (e f : CompleteEdge (n + 1)) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    x ∈ crossingPoints (deleteDrawing D v).toContinuousDrawing ↔
      e.val.1 ≠ v ∧ e.val.2 ≠ v ∧ f.val.1 ≠ v ∧ f.val.2 ≠ v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have ha' := (Paper170Geometry.crossing_incident_iff D x e f hef he hf
      (deletionEdge v a)).mp ha
    have hb' := (Paper170Geometry.crossing_incident_iff D x e f hef he hf
      (deletionEdge v b)).mp hb
    have hab' : deletionEdge v a ≠ deletionEdge v b :=
      fun h => hab (deletionEdge_injective v h)
    have hae := (deletionEdge_range v (deletionEdge v a)).mp ⟨a, rfl⟩
    have hbe := (deletionEdge_range v (deletionEdge v b)).mp ⟨b, rfl⟩
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact (hab' (ha'.trans hb'.symm)).elim
    · simpa [ha', hb', and_assoc] using And.intro hae hbe
    · simpa [ha', hb', and_assoc] using And.intro hbe hae
    · exact (hab' (ha'.trans hb'.symm)).elim
  · rintro ⟨he1, he2, hf1, hf2⟩
    obtain ⟨a, ha⟩ := (deletionEdge_range v e).mpr ⟨he1, he2⟩
    obtain ⟨b, hb⟩ := (deletionEdge_range v f).mpr ⟨hf1, hf2⟩
    refine ⟨a, b, ?_, ?_, ?_⟩
    · intro h
      exact hef (ha.symm.trans ((congrArg (deletionEdge v) h).trans hb))
    · change x ∈ edgeInterior D.toContinuousDrawing (deletionEdge v a)
      simpa [ha] using he
    · change x ∈ edgeInterior D.toContinuousDrawing (deletionEdge v b)
      simpa [hb] using hf

end Paper170

end
end

section

noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170

lemma crossing_endpoints_distinct {n : ℕ} (N : NormalizedDrawing (completeGraph n))
    (x : Plane) (e f : CompleteEdge n) (hef : e ≠ f)
    (he : x ∈ edgeInterior N.toContinuousDrawing e)
    (hf : x ∈ edgeInterior N.toContinuousDrawing f) :
    e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2 ∧ e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2 := by
  have hn : ¬ (e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 ∨
      e.val.2 = f.val.1 ∨ e.val.2 = f.val.2) := by
    intro h
    exact Set.disjoint_left.mp (N.no_adjacent e f hef h) he hf
  tauto

lemma deletion_survivor_card {n : ℕ} (N : NormalizedDrawing (completeGraph (n + 1)))
    (x : Plane) (hx : x ∈ crossingPoints N.toContinuousDrawing) :
    (Finset.univ.filter (fun v : Fin (n + 1) =>
      x ∈ crossingPoints (deleteDrawing N.toAdmissibleDrawing v).toContinuousDrawing)).card =
      n + 1 - 4 := by
  obtain ⟨e, f, hef, he, hf⟩ := hx
  rcases crossing_endpoints_distinct N x e f hef he hf with ⟨h13, h14, h23, h24⟩
  have h12 : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have h34 : f.val.1 ≠ f.val.2 := ne_of_lt f.property
  simp_rw [deletion_crossing_iff N.toAdmissibleDrawing _ x e f hef he hf]
  have hset : Finset.univ.filter (fun v : Fin (n + 1) =>
      e.val.1 ≠ v ∧ e.val.2 ≠ v ∧ f.val.1 ≠ v ∧ f.val.2 ≠ v) =
      Finset.univ \ {e.val.1, e.val.2, f.val.1, f.val.2} := by
    ext v
    simp [eq_comm]
  rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [h12, h13, h14, h23, h24, h34]

lemma deleteDrawing_count_filter {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) :
    crossingCount (deleteDrawing D v) = (D.crossings_finite.toFinset.filter fun x =>
      x ∈ crossingPoints (deleteDrawing D v).toContinuousDrawing).card := by
  unfold crossingCount
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨deletion_crossings_subset D.toContinuousDrawing v h, h⟩, And.right⟩

theorem vertex_deletion_count (n : ℕ) (_hn : 4 ≤ n)
    (N : NormalizedDrawing (completeGraph (n + 1))) :
    ∃ A : Fin (n + 1) → AdmissibleDrawing (completeGraph n),
      (∀ v, VertexDeletion N.toAdmissibleDrawing v (A v)) ∧
      (∑ v, crossingCount (A v)) = (n + 1 - 4) * crossingCount N.toAdmissibleDrawing := by
  refine ⟨deleteDrawing N.toAdmissibleDrawing, deleteDrawing_spec N.toAdmissibleDrawing, ?_⟩
  simp_rw [deleteDrawing_count_filter, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ N.crossings_finite.toFinset,
      ∑ v : Fin (n + 1), if x ∈ crossingPoints
        (deleteDrawing N.toAdmissibleDrawing v).toContinuousDrawing then 1 else 0) =
        ∑ _x ∈ N.crossings_finite.toFinset, (n + 1 - 4) := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [Finset.card_filter] using
        deletion_survivor_card N x (by simpa using hx)
    _ = (n + 1 - 4) * crossingCount N.toAdmissibleDrawing := by
      simp [crossingCount, Nat.mul_comm]

end Paper170

end
end

end OAI

import OAI.Combinatorics.Ryser.Geometry.Basic
import OAI.Combinatorics.Ryser.Hypergraph.Partite
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

structure ConfigurationData (k F G : Type*) [DecidableEq F] where
  altered : G → Finset (Direction F)
  inverseSlope : ∀ i, {d : Direction F // d ∈ altered i} → k
  base : G → Point k → Point F
  transform : Point k → Point k
  retained : Finset (Point k)
  ordinaryPoints : Finset (Point F)

abbrev Vertex {k F G : Type*} [DecidableEq F]
    (altered : G → Finset (Direction F)) :=
  AffineLine F ⊕ (Σ i : G, {d : Direction F // d ∈ altered i} × k)

variable {k F G : Type*} [instFieldk : Field k] [instFieldF : Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]

def ordinaryVertex (data : ConfigurationData k F G) (ell : AffineLine F) :
    Vertex (k := k) data.altered := Sum.inl ell

def specialVertex (data : ConfigurationData k F G) (i : G)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    Vertex (k := k) data.altered := Sum.inr ⟨i, (d, c)⟩

def vertexPart (data : ConfigurationData k F G) :
    Vertex (k := k) data.altered → Direction F
  | Sum.inl ell => ell.1
  | Sum.inr v => v.2.1.val

@[simp] theorem vertexPart_ordinaryVertex (data : ConfigurationData k F G)
    (ell : AffineLine F) : vertexPart data (ordinaryVertex data ell) = ell.1 := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; rfl

@[simp] theorem vertexPart_specialVertex (data : ConfigurationData k F G) (i : G)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    vertexPart data (specialVertex data i d c) = d.val := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; rfl

def exceptionalVertex (data : ConfigurationData k F G) (i : G) (w : Point k)
    (d : Direction F) : Vertex (k := k) data.altered :=
  if h : d ∈ data.altered i then
    specialVertex data i ⟨d, h⟩
      (projection (some (data.inverseSlope i ⟨d, h⟩)) (data.transform w))
  else ordinaryVertex data (lineThrough d (data.base i w))

theorem exceptionalVertex_of_mem (data : ConfigurationData k F G) (i : G)
    (w : Point k) (d : Direction F) (hd : d ∈ data.altered i) :
    exceptionalVertex data i w d = specialVertex data i ⟨d, hd⟩
      (projection (some (data.inverseSlope i ⟨d, hd⟩)) (data.transform w)) := let _ := instDecidableEqk; let _ := instDecidableEqG; by
  simp only [exceptionalVertex, dite_eq_left hd]

theorem exceptionalVertex_of_notMem (data : ConfigurationData k F G) (i : G)
    (w : Point k) (d : Direction F) (hd : d ∉ data.altered i) :
    exceptionalVertex data i w d = ordinaryVertex data (lineThrough d (data.base i w)) := let _ := instDecidableEqk; let _ := instDecidableEqG; by
  simp only [exceptionalVertex, dite_eq_right hd]

@[simp] theorem vertexPart_exceptionalVertex (data : ConfigurationData k F G)
    (i : G) (w : Point k) (d : Direction F) :
    vertexPart data (exceptionalVertex data i w d) = d := by
  by_cases hd : d ∈ data.altered i
  · rw [exceptionalVertex_of_mem data i w d hd]
    rfl
  · rw [exceptionalVertex_of_notMem data i w d hd]
    rfl

variable [Fintype F]

def ordinaryEdge (data : ConfigurationData k F G) (x : Point F) :
    Finset (Vertex (k := k) data.altered) :=
  Finset.univ.image (fun d => ordinaryVertex data (lineThrough d x))

def exceptionalEdge (data : ConfigurationData k F G) (i : G) (w : Point k) :
    Finset (Vertex (k := k) data.altered) :=
  Finset.univ.image (exceptionalVertex data i w)

theorem ordinaryVertex_mem_ordinaryEdge (data : ConfigurationData k F G)
    (x : Point F) (d : Direction F) :
    ordinaryVertex data (lineThrough d x) ∈ ordinaryEdge data x := let _ := instFieldk;
  Finset.mem_image_of_mem _ (Finset.mem_univ d)

theorem exceptionalVertex_mem_exceptionalEdge (data : ConfigurationData k F G)
    (i : G) (w : Point k) (d : Direction F) :
    exceptionalVertex data i w d ∈ exceptionalEdge data i w :=
  Finset.mem_image_of_mem _ (Finset.mem_univ d)

theorem selector_edge_partite {I V : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq V] (part : V → I) (selector : I → V)
    (hpart : ∀ i, part (selector i) = i) :
    ∀ i, ∃! v, v ∈ Finset.univ.image selector ∧ part v = i := by
  intro i
  refine ⟨selector i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), hpart i⟩, ?_⟩
  rintro v ⟨hv, hvi⟩
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  rw [hpart j] at hvi
  exact congrArg selector hvi

theorem mem_selector_edge_iff {I V : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq V] (part : V → I) (selector : I → V)
    (hpart : ∀ i, part (selector i) = i) (v : V) :
    v ∈ Finset.univ.image selector ↔ v = selector (part v) := by
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    rw [hpart i]
  · intro hv
    rw [hv]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem ordinaryEdge_partite (data : ConfigurationData k F G) (x : Point F) :
    ∀ d, ∃! v, v ∈ ordinaryEdge data x ∧ vertexPart data v = d := let _ := instFieldk;
  selector_edge_partite (vertexPart data)
    (fun d => ordinaryVertex data (lineThrough d x)) (fun _ => rfl)

theorem exceptionalEdge_partite (data : ConfigurationData k F G) (i : G)
    (w : Point k) :
    ∀ d, ∃! v, v ∈ exceptionalEdge data i w ∧ vertexPart data v = d :=
  selector_edge_partite (vertexPart data) (exceptionalVertex data i w)
    (vertexPart_exceptionalVertex data i w)

theorem mem_exceptionalEdge_iff (data : ConfigurationData k F G) (i : G)
    (w : Point k) (v : Vertex (k := k) data.altered) :
    v ∈ exceptionalEdge data i w ↔
      v = exceptionalVertex data i w (vertexPart data v) :=
  mem_selector_edge_iff (vertexPart data) (exceptionalVertex data i w)
    (vertexPart_exceptionalVertex data i w) v

variable [Fintype G]

def hypergraph (data : ConfigurationData k F G) :
    Hypergraph (Vertex (k := k) data.altered) := by
  classical
  exact data.ordinaryPoints.image (ordinaryEdge data) ∪
    Finset.univ.biUnion (fun i => data.retained.image (exceptionalEdge data i))

@[simp] theorem mem_hypergraph (data : ConfigurationData k F G)
    (e : Finset (Vertex (k := k) data.altered)) :
    e ∈ hypergraph data ↔
      (∃ x ∈ data.ordinaryPoints, ordinaryEdge data x = e) ∨
      (∃ i, ∃ w ∈ data.retained, exceptionalEdge data i w = e) := by
  classical
  simp only [hypergraph, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_univ, true_and]

theorem hypergraph_partite (data : ConfigurationData k F G) :
    PartiteUniform (vertexPart data) (hypergraph data) := by
  intro e he
  rcases (mem_hypergraph data e).mp he with ⟨x, _, rfl⟩ | ⟨i, w, _, rfl⟩
  · exact ordinaryEdge_partite data x
  · exact exceptionalEdge_partite data i w

theorem hypergraph_uniform (data : ConfigurationData k F G) :
    Uniform (Fintype.card F + 1) (hypergraph data) := by
  simpa only [Fintype.card_option] using (hypergraph_partite data).uniform

theorem hypergraph_rPartiteUniform (data : ConfigurationData k F G) :
    RPartiteUniform (Fintype.card F + 1) (hypergraph data) := by
  simpa only [Fintype.card_option] using (hypergraph_partite data).rPartiteUniform

theorem hypergraph_nonempty (data : ConfigurationData k F G) (i : G)
    (hY : data.retained.Nonempty) : (hypergraph data).Nonempty := by
  obtain ⟨w, hw⟩ := hY
  refine ⟨exceptionalEdge data i w, (mem_hypergraph data _).mpr ?_⟩
  exact Or.inr ⟨i, w, hw, rfl⟩

end RyserCoveringCounterexample.Construction

end

end OAI

import OAI.Probability.CriticalZ3.BoxGeometry

namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

inductive Model | bond | site

namespace Model
abbrev Bit : Model → Type
  | bond => Bond
  | site => Vertex
abbrev Config (m : Model) := m.Bit → Bool
instance (m : Model) : Countable m.Bit := by cases m <;> infer_instance
instance (m : Model) : DecidableEq m.Bit := by cases m <;> infer_instance
end Model

namespace Box
noncomputable def bits (B : Box) : (m : Model) → Finset m.Bit
  | .bond => B.bonds
  | .site => B.vertices
end Box

namespace LatticeGraph
variable (G : LatticeGraph)
noncomputable def bits : (m : Model) → Finset m.Bit
  | .bond => G.edges
  | .site => G.vertices

def Open : (m : Model) → m.Config → G.Node → Prop
  | .bond,_,_ => True
  | .site,ω,x => ω x.1 = true

def Adj : (m : Model) → m.Config → G.Node → G.Node → Prop
  | .bond,ω,x,y => G.BondAdj ω x y
  | .site,ω,x,y => G.graph.Adj x y ∧ ω x.1 = true ∧ ω y.1 = true

def Conn : (m : Model) → m.Config → G.Node → G.Node → Prop
  | .bond,ω,x,y => G.BondConn ω x y
  | .site,ω,x,y => G.SiteConn ω x y

def Meets (m : Model) (ω : m.Config) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.Conn m ω o y

theorem conn_iff (m : Model) (ω : m.Config) (x y : G.Node) :
    G.Conn m ω x y ↔ G.Open m ω x ∧ Relation.ReflTransGen (G.Adj m ω) x y := by
  cases m
  · exact ⟨fun h => ⟨trivial,h⟩,fun h => h.2⟩
  · rfl

theorem adj_open (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Open m ω x ∧ G.Open m ω y := by
  cases m
  · exact ⟨trivial,trivial⟩
  · exact h.2

theorem adj_neighbor (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    NearestNeighbor x.1 y.1 := by
  cases m
  · obtain ⟨e,_,he,_⟩ := h; exact incidence_neighbor he
  · obtain ⟨⟨e,_,he⟩,_⟩ := h; exact incidence_neighbor he

theorem adj_symm (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Adj m ω y x := by
  cases m
  · obtain ⟨e,he,hi,ho⟩ := h; exact ⟨e,he,incidence_symm hi,ho⟩
  · exact ⟨G.graph.adj_symm h.1,h.2.2,h.2.1⟩

theorem conn_open (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Conn m ω x y) :
    G.Open m ω x ∧ G.Open m ω y := by
  obtain ⟨hx,h⟩ := (G.conn_iff m ω x y).mp h
  refine ⟨hx,?_⟩
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact (G.adj_open m hab).2

theorem conn_symm (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Conn m ω x y) :
    G.Conn m ω y x := by
  refine (G.conn_iff m ω y x).mpr ⟨(G.conn_open m h).2,?_⟩
  have hh := (G.conn_iff m ω x y).mp h |>.2
  clear h
  induction hh with
  | refl => exact .refl
  | tail _ hab ih => exact ih.head (G.adj_symm m hab)

theorem conn_trans (m : Model) {ω : m.Config} {x y z : G.Node}
    (h : G.Conn m ω x y) (h' : G.Conn m ω y z) : G.Conn m ω x z := by
  exact (G.conn_iff m ω x z).mpr ⟨((G.conn_iff m ω x y).mp h).1,
    ((G.conn_iff m ω x y).mp h).2.trans ((G.conn_iff m ω y z).mp h').2⟩

theorem conn_adj (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Conn m ω x y := (G.conn_iff m ω x y).mpr ⟨(G.adj_open m h).1,.single h⟩

theorem conn_determined (m : Model) (ω ω' : m.Config)
    (h : ∀ e ∈ G.bits m, ω' e = ω e) (x y : G.Node) :
    G.Conn m ω' x y ↔ G.Conn m ω x y := by
  cases m
  · exact G.bondConn_determined ω ω' h x y
  · exact G.siteConn_determined ω ω' h x y

theorem meets_determined (m : Model) (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) (G.bits m) (fun ω => G.Meets m ω o T) := by
  intro ω ω' h
  apply propext
  simp only [Meets,G.conn_determined m ω ω' h]

theorem measurableSet_meets (m : Model) (o : G.Node) (T : Set Vertex) :
    MeasurableSet {ω | G.Meets m ω o T} :=
  ProductCylinder.measurableSet_determined _ _ (fun ω ω' h =>
    eq_iff_iff.mp (G.meets_determined m o T ω ω' h))

theorem failure_comparison (m : Model) (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.Meets m ω a T}) :
    (ProductCylinder.law p).real {ω | G.Meets m ω o A ∧ ¬G.Meets m ω o T} ≤ b := by
  cases m
  · exact G.bond_failure_comparison p o A T hb0 hb
  · exact G.site_failure_comparison p o A T hb0 hb

def ContainsBox (B : Box) : Prop := B.vertices ⊆ G.vertices ∧ B.bonds ⊆ G.edges

theorem containsBox_node {B : Box} (h : G.ContainsBox B) {x : Vertex}
    (hx : B.Contains x) : x ∈ G.vertices := h.1 ((B.mem_vertices x).mpr hx)

theorem neighbor_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ e : Bond, Incidence e x y := by
  obtain ⟨i,h | h⟩ := h
  · exact ⟨(x,i),Or.inl ⟨rfl,h⟩⟩
  · exact ⟨(y,i),Or.inr ⟨rfl,h⟩⟩

theorem incidence_internal {B : Box} {x y : Vertex} {e : Bond}
    (hx : B.Contains x) (hy : B.Contains y) (he : Incidence e x y) : e ∈ B.bonds := by
  rw [Box.mem_bonds]
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hx,hy⟩
  · exact ⟨hy,hx⟩

theorem open_box_adj (m : Model) {B : Box} (hB : G.ContainsBox B)
    {ω : m.Config} (ho : ∀ e ∈ B.bits m, ω e = true) {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) (hxy : NearestNeighbor x.1 y.1) :
    G.Adj m ω x y := by
  obtain ⟨e,he⟩ := neighbor_incidence hxy
  have heb := incidence_internal hx hy he
  cases m
  · exact ⟨e,hB.2 heb,he,ho e heb⟩
  · exact ⟨⟨e,hB.2 heb,he⟩,ho x.1 ((B.mem_vertices x.1).mpr hx),
      ho y.1 ((B.mem_vertices y.1).mpr hy)⟩

/-- Lifting a vertex path into a finite graph, retaining the exact endpoints. -/
theorem lift_path {r : Vertex → Vertex → Prop} {s : G.Node → G.Node → Prop}
    (hmem : ∀ x y, r x y → y ∈ G.vertices)
    (hrel : ∀ (x y : G.Node), r x.1 y.1 → s x y)
    {x y : G.Node} (h : Relation.ReflTransGen r x.1 y.1) : Relation.ReflTransGen s x y := by
  have hh : ∀ {z : Vertex}, Relation.ReflTransGen r x.1 z →
      ∀ hz : z ∈ G.vertices, Relation.ReflTransGen s x ⟨z,hz⟩ := by
    intro z hp
    induction hp with
    | refl => intro _; exact .refl
    | @tail a b ha hab ih =>
      intro hb
      rcases ha.cases_tail with hxa | ⟨u,hu,hua⟩
      · subst a
        exact Relation.ReflTransGen.single (hrel x ⟨b,hb⟩ hab)
      · have ham := hmem u a hua
        exact (ih ham).tail (hrel ⟨a,ham⟩ ⟨b,hb⟩ hab)
  exact hh h y.2

theorem open_box_conn (m : Model) {B : Box} (hB : G.ContainsBox B)
    {ω : m.Config} (ho : ∀ e ∈ B.bits m, ω e = true) {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) : G.Conn m ω x y := by
  apply (G.conn_iff m ω x y).mpr
  constructor
  · cases m
    · trivial
    · exact ho x.1 ((B.mem_vertices x.1).mpr hx)
  · apply G.lift_path (r := B.Within)
      (fun _ _ h => G.containsBox_node hB h.2.2)
      (fun x y h => G.open_box_adj m hB ho h.2.1 h.2.2 h.1)
    exact B.connected hx hy

end LatticeGraph
end CriticalZ3

end OAI

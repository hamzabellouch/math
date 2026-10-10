import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedron

namespace OAI

/-! A finite simplicial model of a literal finite polygon incidence system.
All edges are split three times, and every boundary occurrence has its own
collar vertex. Thus loops, repeated boundary vertices and parallel edges are
not silently identified. The carrier/homotopy comparison is a later theorem. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel
open FinitePolyhedron

structure Data (V E C : Type*) where
  size : C → ℕ
  positive : ∀ c, 0 < size c
  start : E × Bool → V
  side : (c : C) → Fin (size c) → E × Bool
  closed : ∀ c i, start (side c (finRotate (size c) i)) =
    start ((side c i).1, !(side c i).2)

namespace Data
variable {V E C : Type*}
variable (P : Data V E C)

abbrev Position := (c : C) × (Fin (P.size c) × Fin 3)
abbrev GraphVertex := V ⊕ (E × Bool)
abbrev Vertex := GraphVertex (V := V) (E := E) ⊕ (C ⊕ P.Position)

abbrev graph (v : GraphVertex (V := V) (E := E)) : P.Vertex := .inl v
abbrev old (v : V) : P.Vertex := P.graph (.inl v)
abbrev mid (e : E) (b : Bool) : P.Vertex := P.graph (.inr (e,b))
abbrev apex (c : C) : P.Vertex := .inr (.inl c)
abbrev outer (q : P.Position) : P.Vertex := .inr (.inr q)

def next (q : P.Position) : P.Position :=
  ⟨q.1, if h : q.2.2.val = 2 then (finRotate (P.size q.1) q.2.1,0)
    else (q.2.1,⟨q.2.2.val+1,by omega⟩)⟩

lemma next_ne (q : P.Position) : P.next q ≠ q := by
  rcases q with ⟨c,i,j⟩
  intro h
  have hh := congrArg (fun a : P.Position => a.2.2.val) h
  simp only [Data.next] at hh
  split_ifs at hh with hj
  · change (0 : ℕ) = j.val at hh
    omega
  · change j.val + 1 = j.val at hh
    omega

/-- Start of one of the three subdivided segments of a signed old edge. -/
def dartStart (e : E × Bool) (j : Fin 3) : P.Vertex :=
  if j.val = 0 then P.old (P.start e)
  else if j.val = 1 then P.mid e.1 e.2 else P.mid e.1 (!e.2)

def base (q : P.Position) : P.Vertex := P.dartStart (P.side q.1 q.2.1) q.2.2

variable [DecidableEq V] [DecidableEq E] [DecidableEq C]

/-- The three positive graph segments. -/
def graphFace (e : E) (j : Fin 3) : Finset P.Vertex :=
  if j.val = 0 then {P.old (P.start (e,true)),P.mid e true}
  else if j.val = 1 then {P.mid e true,P.mid e false}
  else {P.mid e false,P.old (P.start (e,false))}

/-- Two simplices in each mapping-cylinder rectangle and one cap simplex. -/
def collarFace (q : P.Position) (j : Fin 3) : Finset P.Vertex :=
  if j.val = 0 then {P.outer q,P.base q,P.base (P.next q)}
  else if j.val = 1 then {P.outer q,P.outer (P.next q),P.base (P.next q)}
  else {P.outer q,P.outer (P.next q),P.apex q.1}

abbrev Facet := (E × Fin 3) ⊕ (P.Position × Fin 3)
def facet : P.Facet → Finset P.Vertex
  | .inl e => P.graphFace e.1 e.2
  | .inr q => P.collarFace q.1 q.2

def complex : AbstractSimplicialComplex P.Vertex where
  faces := {s | s.Nonempty ∧ (s.card ≤ 1 ∨ ∃ f : P.Facet, s ⊆ P.facet f)}
  isRelLowerSet_faces := by
    rintro s ⟨hs,h⟩
    refine ⟨hs,fun t hts ht => ⟨ht,?_⟩⟩
    rcases h with h|⟨f,hf⟩
    · exact Or.inl ((Finset.card_le_card hts).trans h)
    · exact Or.inr ⟨f,hts.trans hf⟩
  singleton_mem := fun v => ⟨Finset.singleton_nonempty v,Or.inl (by simp)⟩

lemma facet_face (f : P.Facet) : P.facet f ∈ P.complex.faces := by
  refine ⟨?_,Or.inr ⟨f,Finset.Subset.refl _⟩⟩
  cases f with
  | inl e => dsimp [facet,graphFace]; split_ifs <;> simp
  | inr q => dsimp [facet,collarFace]; split_ifs <;> simp

lemma simplex_card_le_three {s : Finset P.Vertex} (hs : s ∈ P.complex.faces) : s.card ≤ 3 := by
  have ht (a b c : P.Vertex) : ({a,b,c} : Finset P.Vertex).card ≤ 3 :=
    (Finset.card_insert_le a {b,c}).trans (Nat.add_le_add_right Finset.card_le_two 1)
  rcases hs.2 with h|⟨f,hf⟩
  · omega
  · apply (Finset.card_le_card hf).trans
    cases f with
    | inl e => dsimp [facet,graphFace]; split_ifs <;> exact Finset.card_le_two.trans (by decide)
    | inr q => dsimp [facet,collarFace]; split_ifs <;> exact ht _ _ _

lemma edge_of_facet (f : P.Facet) {a b : P.Vertex} (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) :
    {a,b} ∈ P.complex.faces := by
  refine ⟨by simp,Or.inr ⟨f,?_⟩⟩
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl <;> assumption

variable [Fintype V] [Fintype E] [Fintype C]

lemma joined_of_facet (f : P.Facet) {a b : P.Vertex} (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) :
    Joined (vertex P.complex a) (vertex P.complex b) :=
  vertex_joined_of_edge P.complex (P.edge_of_facet f ha hb)

lemma mid_joined_start (e : E) (b : Bool) :
    Joined (vertex P.complex (P.mid e b)) (vertex P.complex (P.old (P.start (e,b)))) := by
  cases b
  · exact P.joined_of_facet (.inl (e,2)) (by simp [facet,graphFace]) (by simp [facet,graphFace])
  · exact P.joined_of_facet (.inl (e,0)) (by simp [facet,graphFace]) (by simp [facet,graphFace])

lemma endpoints_joined (e : E) :
    Joined (vertex P.complex (P.old (P.start (e,true))))
      (vertex P.complex (P.old (P.start (e,false)))) :=
  (P.mid_joined_start e true).symm.trans
    ((P.joined_of_facet (.inl (e,1)) (by simp [facet,graphFace]) (by simp [facet,graphFace])).trans
      (P.mid_joined_start e false))

lemma outer_joined_base (q : P.Position) :
    Joined (vertex P.complex (P.outer q)) (vertex P.complex (P.base q)) :=
  P.joined_of_facet (.inr (q,0)) (by simp [facet,collarFace]) (by simp [facet,collarFace])

lemma apex_joined_outer (c : C) :
    Joined (vertex P.complex (P.apex c))
      (vertex P.complex (P.outer ⟨c,(⟨0,P.positive c⟩,0)⟩)) :=
  P.joined_of_facet (.inr (⟨c,(⟨0,P.positive c⟩,0)⟩,2))
    (by simp [facet,collarFace]) (by simp [facet,collarFace])

/-- Connectedness is reduced exactly to the old graph, not assumed for the
new carrier. -/
lemma pathConnected_of_graph (v : V)
    (h : ∀ w : V, Joined (vertex P.complex (P.old v)) (vertex P.complex (P.old w))) :
    PathConnectedSpace (Carrier P.complex) := by
  have hm : ∀ e b, Joined (vertex P.complex (P.old v)) (vertex P.complex (P.mid e b)) :=
    fun e b => (h (P.start (e,b))).trans (P.mid_joined_start e b).symm
  have hb : ∀ q, Joined (vertex P.complex (P.old v)) (vertex P.complex (P.base q)) := by
    intro q
    dsimp [base,dartStart]
    split_ifs
    · exact h _
    · exact hm _ _
    · exact hm _ _
  have ho : ∀ q, Joined (vertex P.complex (P.old v)) (vertex P.complex (P.outer q)) :=
    fun q => (hb q).trans (P.outer_joined_base q).symm
  apply pathConnected_of_vertex_connected P.complex (P.old v)
  rintro ((w|⟨e,b⟩)|(c|q))
  · exact h w
  · exact hm e b
  · exact (ho _).trans (P.apex_joined_outer c).symm
  · exact ho q

end Data
end HyperbolicObstruction.FinitePolygonModel
end

end OAI

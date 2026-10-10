import OAI.NumberTheory.TwoPoint.Walks.IncidenceForest

namespace OAI

/-! Concrete alternating run/transition lists give reduced incidence walks. -/

namespace TwoPointCorrelations

open SimpleGraph

variable {V : Type*}

def NoImmediateReturn : List V → Prop
  | a :: b :: c :: rest => a ≠ c ∧ NoImmediateReturn (b :: c :: rest)
  | _ => True

theorem walk_reduced_iff_noImmediateReturn {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : List.IsChain (· ≠ ·) p.edges ↔ NoImmediateReturn p.support := by
  induction p with
  | nil => simp [NoImmediateReturn]
  | @cons a b c hab p ih =>
      cases p with
      | nil => simp [NoImmediateReturn]
      | @cons b d c hbd q =>
          have he : s(a, b) ≠ s(b, d) ↔ a ≠ d := by
            simp [hab.ne]
          simp only [Walk.edges_cons, List.isChain_cons_cons, Walk.support_cons] at ih ⊢
          rw [← Walk.cons_tail_support q] at ih ⊢
          exact and_congr he ih

theorem vertex_list_isPath {G : SimpleGraph V} (hG : G.IsAcyclic)
    (l : List V) (hne : l ≠ []) (hchain : l.IsChain G.Adj) (hreturn : NoImmediateReturn l) :
    (Walk.ofSupport l hne hchain).IsPath := by
  apply (hG.isPath_iff_isChain _).mpr
  apply (walk_reduced_iff_noImmediateReturn _).mpr
  simpa only [Walk.support_ofSupport] using hreturn

variable {K ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Each pair records a transition point and the next run label. -/
def incidenceVertices (i : ι) : List (V × ι) → List (ι ⊕ V)
  | [] => [.inl i]
  | (x, j) :: rest => .inl i :: .inr x :: incidenceVertices j rest

def IncidenceChain (anchor d : ι → V) (i : ι) : List (V × ι) → Prop
  | [] => True
  | (x, j) :: rest =>
      (∃ t : K, x = anchor i + t • d i) ∧
      (∃ t : K, x = anchor j + t • d j) ∧ IncidenceChain anchor d j rest

/-- Adjacent run labels differ, and consecutive transition points differ.
The latter is exactly the nonzero run-increment condition. -/
def IncidenceReduced (i : ι) : List (V × ι) → Prop
  | [] => True
  | (x, j) :: rest => i ≠ j ∧
      (∀ y k, rest.head? = some (y, k) → x ≠ y) ∧ IncidenceReduced j rest

omit [AddCommGroup V] in
lemma incidenceVertices_ne_nil (i : ι) (steps : List (V × ι)) :
    incidenceVertices i steps ≠ [] := by
  cases steps <;> simp [incidenceVertices]

theorem incidenceVertices_isChain (anchor d : ι → V) (i : ι) (steps : List (V × ι))
    (h : IncidenceChain (K := K) anchor d i steps) :
    (incidenceVertices i steps).IsChain (affineIncidenceGraph (K := K) anchor d).Adj := by
  induction steps generalizing i with
  | nil => exact .singleton _
  | cons step rest ih =>
      rcases step with ⟨x, j⟩
      rcases h with ⟨hi, hj, hrest⟩
      have htail := ih j hrest
      cases rest with
      | nil => exact .cons_cons hi (.cons_cons hj (.singleton _))
      | cons step rest => exact .cons_cons hi (.cons_cons hj htail)

omit [AddCommGroup V] in
theorem incidenceVertices_noImmediateReturn (i : ι) (steps : List (V × ι))
    (h : IncidenceReduced i steps) : NoImmediateReturn (incidenceVertices i steps) := by
  induction steps generalizing i with
  | nil => trivial
  | cons step rest ih =>
      rcases step with ⟨x, j⟩
      rcases h with ⟨hij, hpoint, hrest⟩
      have htail := ih j hrest
      cases rest with
      | nil => simpa [incidenceVertices, NoImmediateReturn] using hij
      | cons step rest =>
          rcases step with ⟨y, k⟩
          have hxy : x ≠ y := hpoint y k rfl
          change (Sum.inl i : ι ⊕ V) ≠ Sum.inl j ∧
            (Sum.inr x : ι ⊕ V) ≠ Sum.inr y ∧ _
          exact ⟨fun h => hij (Sum.inl.inj h), fun h => hxy (Sum.inr.inj h), htail⟩

/-- The actual alternating incidence walk is simple. In particular, its
line sequence is determined by its two endpoints in the forest. -/
theorem incidence_vertices_simple (anchor d : ι → V) (hd : LinearIndependent K d)
    (i : ι) (steps : List (V × ι))
    (hc : IncidenceChain (K := K) anchor d i steps) (hr : IncidenceReduced i steps) :
    (Walk.ofSupport (incidenceVertices i steps) (incidenceVertices_ne_nil i steps)
      (incidenceVertices_isChain anchor d i steps hc)).IsPath :=
  vertex_list_isPath (affineIncidenceGraph_isAcyclic anchor d hd) _ _ _
    (incidenceVertices_noImmediateReturn i steps hr)

end TwoPointCorrelations

end OAI

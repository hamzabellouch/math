import OAI.Computability.PerfectCompleteness.Foundations.SourceStrategy

namespace OAI

section

namespace PerfectCompleteness.SourceCompleteness

open SourceClause ClauseSupport MixedSupport CanonicalKeys SourceKeys

variable {v m n : Nat} {Y Z : Type*}

structure Presentation (clauses : Fin m → NormalizedClause v) (n : Nat) (Y : Type*) where
  endpoints : Fin n → Endpoint v m
  joint : Assignment (slot clauses ∘ endpoints) → Y

variable {clauses : Fin m → NormalizedClause v} {side : Side}

noncomputable def presentationKey (side : Side) (P : Presentation clauses n Y) : Key n :=
  key side (slot clauses ∘ P.endpoints) P.joint

noncomputable def generatedKeys (side : Side) (clauses : Fin m → NormalizedClause v)
    (n : Nat) (Y : Type*) : Set (Key n) :=
  Set.range (presentationKey (clauses := clauses) (n := n) (Y := Y) side)

abbrev Vertex (side : Side) (clauses : Fin m → NormalizedClause v) (n : Nat) (Y : Type*) :=
  ↥(generatedKeys side clauses n Y)

noncomputable def vertexOf (side : Side) (P : Presentation clauses n Y) :
    Vertex side clauses n Y :=
  ⟨presentationKey side P, ⟨P, rfl⟩⟩

abbrev VertexLabel (vertex : Vertex side clauses n Y) :=
  {part : Set (Fin n → ReducedValue) // part ∈ vertex.val.partition}

noncomputable def representation (vertex : Vertex side clauses n Y) :
    Presentation clauses n Y :=
  vertex.property.choose

theorem representation_key (vertex : Vertex side clauses n Y) :
    presentationKey side (representation vertex) = vertex.val :=
  vertex.property.choose_spec

noncomputable def evaluatedLabel (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (P : Presentation clauses n Y) : Label (slot clauses ∘ P.endpoints) P.joint :=
  evaluateLabel (slot clauses ∘ P.endpoints) P.joint
    (realizingAssignment clauses assignment hsat P.endpoints)

noncomputable def strategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (vertex : Vertex side clauses n Y) : VertexLabel vertex := by
  refine ⟨(evaluatedLabel assignment hsat (representation vertex)).val, ?_⟩
  rw [← representation_key vertex]
  exact (evaluatedLabel assignment hsat (representation vertex)).property

theorem strategy_value_eq (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (vertex : Vertex side clauses n Y) (P : Presentation clauses n Z)
    (hkey : presentationKey side P = vertex.val) :
    (strategy assignment hsat vertex).val = (evaluatedLabel assignment hsat P).val := by
  change (evaluatedLabel assignment hsat (representation vertex)).val =
    (evaluatedLabel assignment hsat P).val
  exact evaluated_label_eq_of_key_eq clauses assignment hsat side side
    (representation vertex).endpoints P.endpoints
    (representation vertex).joint P.joint
    ((representation_key vertex).trans hkey.symm)

def labelInPresentation (vertex : Vertex side clauses n Y)
    (P : Presentation clauses n Z) (hkey : presentationKey side P = vertex.val)
    (label : VertexLabel vertex) : Label (slot clauses ∘ P.endpoints) P.joint :=
  ⟨label.val, by
    change label.val ∈ (presentationKey side P).partition
    rw [hkey]
    exact label.property⟩

theorem strategy_in_presentation (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (vertex : Vertex side clauses n Y) (P : Presentation clauses n Z)
    (hkey : presentationKey side P = vertex.val) :
    labelInPresentation vertex P hkey (strategy assignment hsat vertex) =
      evaluatedLabel assignment hsat P := by
  apply Subtype.ext
  exact strategy_value_eq assignment hsat vertex P hkey

theorem restore_strategy_in_presentation (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (vertex : Vertex side clauses n Y) (P : Presentation clauses n Z)
    (hkey : presentationKey side P = vertex.val) :
    restore (slot clauses ∘ P.endpoints) P.joint
        (labelInPresentation vertex P hkey (strategy assignment hsat vertex)) =
      P.joint (realizingAssignment clauses assignment hsat P.endpoints) := by
  rw [strategy_in_presentation]
  exact restore_evaluateLabel _ _ _

def Presentation.postcompose (P : Presentation clauses n Y) (p : Y → Z) :
    Presentation clauses n Z where
  endpoints := P.endpoints
  joint := p ∘ P.joint

noncomputable def coarseningEdge (sourceSide targetSide : Side)
    (P : Presentation clauses n Y) (p : Y → Z)
    (label : VertexLabel (vertexOf sourceSide P)) :
    VertexLabel (vertexOf targetSide (P.postcompose p)) := by
  let original := labelInPresentation (vertexOf sourceSide P) P rfl label
  let coarse := CanonicalEdges.coarsen (slot clauses ∘ P.endpoints) P.joint p original
  exact ⟨coarse.val, coarse.property⟩

theorem coarseningEdge_strategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (sourceSide targetSide : Side) (P : Presentation clauses n Y) (p : Y → Z) :
    coarseningEdge sourceSide targetSide P p
        (strategy assignment hsat (vertexOf sourceSide P)) =
      strategy assignment hsat (vertexOf targetSide (P.postcompose p)) := by
  have hsource : presentationKey sourceSide P = (vertexOf sourceSide P).val := rfl
  have htarget : presentationKey targetSide (P.postcompose p) =
      (vertexOf targetSide (P.postcompose p)).val := rfl
  have hlabel : labelInPresentation (vertexOf sourceSide P) P hsource
      (strategy assignment hsat (vertexOf sourceSide P)) = evaluatedLabel assignment hsat P :=
    strategy_in_presentation assignment hsat (vertexOf sourceSide P) P hsource
  apply Subtype.ext
  calc
    _ = (CanonicalEdges.coarsen (slot clauses ∘ P.endpoints) P.joint p
        (evaluatedLabel assignment hsat P)).val :=
      congrArg (fun L : Label (slot clauses ∘ P.endpoints) P.joint =>
        (CanonicalEdges.coarsen (slot clauses ∘ P.endpoints) P.joint p L).val) hlabel
    _ = (evaluatedLabel assignment hsat (P.postcompose p)).val :=
      congrArg (fun L : Label (slot clauses ∘ P.endpoints) (p ∘ P.joint) => L.val)
        (CanonicalEdges.coarsen_evaluateLabel (slot clauses ∘ P.endpoints) P.joint p
          (realizingAssignment clauses assignment hsat P.endpoints))
    _ = _ := (strategy_value_eq assignment hsat (vertexOf targetSide (P.postcompose p))
      (P.postcompose p) htarget).symm

end PerfectCompleteness.SourceCompleteness

end

end OAI

import OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder
import OAI.NumberTheory.TwoPoint.Walks.ReducedIncidenceWalk

namespace OAI

/-! The regular-part decoder recovers the original run labels. -/

namespace TwoPointCorrelations

variable {ι V W : Type*}

theorem incidenceVertices_length (i : ι) (steps : List (V × ι)) :
    (incidenceVertices i steps).length = 2 * steps.length + 1 := by
  induction steps generalizing i with
  | nil => rfl
  | cons step rest ih =>
      rcases step with ⟨x, j⟩
      simp only [incidenceVertices, List.length_cons, ih]
      omega

/-- Taking even entries removes transition points and retains exactly
the line vertex for each run, also after assigning canonical numbers. -/
theorem evenEntries_incidenceVertices (f : ι ⊕ V → W) (i : ι) (steps : List (V × ι)) :
    evenEntries ((incidenceVertices i steps).map f) =
      (i :: steps.map Prod.snd).map (fun j => f (.inl j)) := by
  induction steps generalizing i with
  | nil => rfl
  | cons step rest ih =>
      rcases step with ⟨x, j⟩
      simpa only [incidenceVertices, List.map_cons, evenEntries] using
        congrArg (fun l => f (.inl i) :: l) (ih j)

theorem evenEntries_incidenceVertices_length (i : ι) (steps : List (V × ι)) :
    (evenEntries (incidenceVertices i steps)).length = steps.length + 1 := by
  have h := evenEntries_incidenceVertices (fun x : ι ⊕ V => x) i steps
  simpa using congrArg List.length h

end TwoPointCorrelations

end OAI

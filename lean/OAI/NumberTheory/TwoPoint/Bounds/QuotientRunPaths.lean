import OAI.NumberTheory.TwoPoint.Bounds.FormalDepartures
import OAI.NumberTheory.TwoPoint.Walks.IncidenceDecoding

namespace OAI

/-! Constant perfect runs give the concrete reduced paths used by column coding. -/

namespace TwoPointCorrelations

open Finset SimpleGraph

variable {K α ι : Type*} [Field K] [Fintype α]

/-- Each transition ends a nonzero constant run and starts the next regular
label on its common quotient line. These are local conditions on departures. -/
def QuotientRunData (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K) (a : ℕ) (i : ι) :
    List (ℕ × ι) → Prop
  | [] => True
  | (b, j) :: rest =>
      a ≤ b ∧ (∀ t ∈ Ico a b, label t = regularLabel i) ∧
      (∑ t ∈ Ico a b, coefficient t) ≠ 0 ∧ i ≠ j ∧
      (∃ c : K, D.mkQ (formalDeparture label coefficient b) = anchor j +
        c • D.mkQ (Pi.basisFun K α (regularLabel j))) ∧
      QuotientRunData D anchor regularLabel label coefficient b j rest

noncomputable def quotientRunSteps (D : Submodule K (α → K)) (label : ℕ → α)
    (coefficient : ℕ → K) (steps : List (ℕ × ι)) : List (((α → K) ⧸ D) × ι) :=
  steps.map (fun p => (D.mkQ (formalDeparture label coefficient p.1), p.2))

/-- Both adjacent lines contain the exact common departure at a transition. -/
theorem quotientRunData_incidenceChain (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K) (a : ℕ) (i : ι) (steps : List (ℕ × ι))
    (hstart : ∃ c : K, D.mkQ (formalDeparture label coefficient a) = anchor i +
      c • D.mkQ (Pi.basisFun K α (regularLabel i)))
    (hdata : QuotientRunData D anchor regularLabel label coefficient a i steps) :
    IncidenceChain (K := K) anchor (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))) i
      (quotientRunSteps D label coefficient steps) := by
  induction steps generalizing a i with
  | nil => trivial
  | cons step rest ih =>
      rcases step with ⟨b, j⟩
      rcases hdata with ⟨hab, hconst, _, _, hnext, hrest⟩
      refine ⟨?_, hnext, ih b j hnext hrest⟩
      exact affine_line_successor _ _ _ _ hstart _
        (quotient_departure_const_run D label coefficient a b hab (regularLabel i) hconst)

/-- Nonzero numerical runs prohibit point--line--point reversal; distinct
adjacent run labels prohibit line--point--line reversal. -/
theorem quotientRunData_reduced (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K)
    (hdir : ∀ j, D.mkQ (Pi.basisFun K α (regularLabel j)) ≠ 0)
    (a : ℕ) (i : ι) (steps : List (ℕ × ι))
    (hdata : QuotientRunData D anchor regularLabel label coefficient a i steps) :
    IncidenceReduced i (quotientRunSteps D label coefficient steps) := by
  induction steps generalizing a i with
  | nil => trivial
  | cons step rest ih =>
      rcases step with ⟨b, j⟩
      rcases hdata with ⟨_, _, _, hij, _, hrest⟩
      refine ⟨hij, ?_, ih b j hrest⟩
      intro y k hhead
      cases rest with
      | nil => simp at hhead
      | cons step rest =>
          rcases step with ⟨c, l⟩
          simp only [List.map_cons, List.head?_cons, Option.some.injEq,
            Prod.mk.injEq] at hhead
          rcases hhead with ⟨rfl, rfl⟩
          rcases hrest with ⟨hbc, hconst, hnonzero, _, _, _⟩
          exact quotient_run_endpoints_ne D label coefficient b c hbc (regularLabel j)
            hconst (hdir j) hnonzero

/-- The path support consists of exactly the canonical regular run lines
alternating with their actual transition departures. -/
theorem quotientRunData_simple (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K)
    (hind : LinearIndependent K (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))))
    (a : ℕ) (i : ι) (steps : List (ℕ × ι))
    (hstart : ∃ c : K, D.mkQ (formalDeparture label coefficient a) = anchor i +
      c • D.mkQ (Pi.basisFun K α (regularLabel i)))
    (hdata : QuotientRunData D anchor regularLabel label coefficient a i steps) :
    (Walk.ofSupport (incidenceVertices i (quotientRunSteps D label coefficient steps))
      (incidenceVertices_ne_nil _ _)
      (incidenceVertices_isChain anchor _ _ _
        (quotientRunData_incidenceChain D anchor regularLabel label coefficient a i steps hstart hdata))).IsPath := by
  exact incidence_vertices_simple anchor _ hind i _
    (quotientRunData_incidenceChain D anchor regularLabel label coefficient a i steps hstart hdata)
    (quotientRunData_reduced D anchor regularLabel label coefficient
      (fun j => hind.ne_zero j) a i steps hdata)

end TwoPointCorrelations

end OAI

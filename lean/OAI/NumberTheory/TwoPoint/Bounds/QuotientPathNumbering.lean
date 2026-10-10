import OAI.NumberTheory.TwoPoint.Walks.IndexedQuotientPaths
import OAI.NumberTheory.TwoPoint.Bounds.FiniteWalkNumbering

namespace OAI

/-! One bounded numbering for the regular lines in all actual quotient paths. -/

namespace TwoPointCorrelations

open Finset SimpleGraph

private theorem inl_mem_incidenceVertices {ι V : Type*} (i j : ι) (steps : List (V × ι)) :
    Sum.inl j ∈ incidenceVertices i steps ↔ j ∈ i :: steps.map Prod.snd := by
  induction steps generalizing i with
  | nil => simp [incidenceVertices]
  | cons step rest ih =>
      rcases step with ⟨x, k⟩
      simp [incidenceVertices, ih]

variable {K α ι : Type*} [Field K] [Fintype α] [DecidableEq ι]

/-- The same forest numbering is used for every regular segment. Equal line
numbers therefore identify exactly equal regular labels across all blocks. -/
theorem quotient_run_family_numbering {S N : ℕ}
    (D : Submodule K (α → K)) (anchor : ι → (α → K) ⧸ D)
    (regularLabel : ι → α) (label : ℕ → α) (coefficient : ℕ → K)
    (hind : LinearIndependent K (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))))
    (start : Fin S → ℕ) (first : Fin S → ι) (steps : Fin S → List (ℕ × ι))
    (hstart : ∀ i, ∃ c : K, D.mkQ (formalDeparture label coefficient (start i)) =
      anchor (first i) + c • D.mkQ (Pi.basisFun K α (regularLabel (first i))))
    (hdata : ∀ i, QuotientRunData D anchor regularLabel label coefficient (start i) (first i) (steps i))
    (hsize : (∑ i, (2 * (steps i).length + 1)) ≤ N) :
    ∃ (number : ι → ℕ) (code : ForestPathData.Code N S),
      (∀ i j, j ∈ first i :: (steps i).map Prod.snd → number j < N) ∧
      (∀ i j, j ∈ first i :: (steps i).map Prod.snd →
        ∀ k l, l ∈ first k :: (steps k).map Prod.snd → number j = number l → j = l) ∧
      ∀ i, evenEntries (decodeForestPaths code i) =
        (first i :: (steps i).map Prod.snd).map number := by
  classical
  let direction := fun j => D.mkQ (Pi.basisFun K α (regularLabel j))
  let G := affineIncidenceGraph (K := K) anchor direction
  let vertices := fun i => incidenceVertices (first i) (quotientRunSteps D label coefficient (steps i))
  have hne : ∀ i, vertices i ≠ [] := fun i => incidenceVertices_ne_nil _ _
  have hchain : ∀ i, (vertices i).IsChain G.Adj := fun i =>
    incidenceVertices_isChain anchor direction (first i) _
      (quotientRunData_incidenceChain D anchor regularLabel label coefficient
        (start i) (first i) (steps i) (hstart i) (hdata i))
  let starts := fun i => (vertices i).head (hne i)
  let finishes := fun i => (vertices i).getLast (hne i)
  let walk : ∀ i, G.Walk (starts i) (finishes i) := fun i =>
    Walk.ofSupport (vertices i) (hne i) (hchain i)
  have hsupport (i : Fin S) : (walk i).support = vertices i :=
    Walk.support_ofSupport (G := G) (hne i) (hchain i)
  have hG : G.IsAcyclic := affineIncidenceGraph_isAcyclic anchor direction hind
  have hred : ∀ i, List.IsChain (· ≠ ·) (walk i).edges := by
    intro i
    apply (hG.isPath_iff_isChain _).mp
    exact quotientRunData_simple D anchor regularLabel label coefficient hind
      (start i) (first i) (steps i) (hstart i) (hdata i)
  have hsize' : (∑ i, (walk i).support.length) ≤ N := by
    simp_rw [hsupport]
    simpa only [vertices, incidenceVertices_length, quotientRunSteps, List.length_map] using hsize
  obtain ⟨number, code, hinj, hbound, hdecode⟩ :=
    finite_walk_family_numbering starts finishes walk hG hred hsize'
      (Sum.elim (fun _ => true) (fun _ => false))
  have hmem : ∀ i j, j ∈ first i :: (steps i).map Prod.snd →
      Sum.inl j ∈ walkFamilySupport starts finishes walk := by
    intro i j hj
    apply mem_walkFamilySupport starts finishes walk i
    rw [hsupport]
    apply (inl_mem_incidenceVertices _ _ _).mpr
    simpa only [quotientRunSteps, List.map_map, Function.comp_def] using hj
  refine ⟨fun j => number (.inl j), code, ?_, ?_, ?_⟩
  · intro i j hj
    exact hbound _ (hmem i j hj)
  · intro i j hj k l hl heq
    exact Sum.inl.inj (hinj (hmem i j hj) (hmem k l hl) heq)
  · intro i
    rw [hdecode]
    rw [hsupport]
    rw [evenEntries_incidenceVertices]
    simp only [quotientRunSteps, List.map_map, Function.comp_def]

end TwoPointCorrelations

end OAI

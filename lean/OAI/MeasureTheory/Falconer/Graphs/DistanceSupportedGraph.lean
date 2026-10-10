import OAI.MeasureTheory.Falconer.Graphs.ActualDistanceDegrees

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphSupportedDistanceIndices (I : Finset GraphNonedgeIndex) (θ axis : ℝ) :
    Finset GraphNonedgeIndex := by
  classical
  exact I.filter (fun e => (tsupport (graphSourceWeight true e.2.2 axis
    (angularBinCount θ) e.2.1.1 e.2.1.2)).Nonempty)

theorem graphOriginalDistanceSum_supported (I : Finset GraphNonedgeIndex)
    (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare) (M : Fin 4 → ℝ)
    (β : Fin 4 → Plane → UnitCircle → ℂ) (θ axis v : ℝ) (Ψ : ℝ → ℝ) :
    (∑ e ∈ I, graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M β
      true e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ) =
    ∑ e ∈ graphSupportedDistanceIndices I θ axis,
      graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M β
        true e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hn
  apply graphOriginalTerm_zero_of_empty_weight_support
  intro hs
  exact hn (Finset.mem_filter.mpr ⟨he,hs⟩)

theorem activeDistanceMatrixNeighbors_eq_supported (I : Finset GraphNonedgeIndex)
    (p j b : ℕ) (θ axis : ℝ) (plus reverse : Bool) (row : CellPath × CellPath) :
    activeDistanceMatrixNeighbors I p j b θ axis plus reverse row =
      distanceMatrixNeighbors (graphSupportedDistanceIndices I θ axis) p j b plus reverse row := by
  classical
  ext col
  cases reverse <;> by_cases hs : (tsupport (graphSourceWeight true plus axis (angularBinCount θ) j b)).Nonempty <;>
    simp [activeDistanceMatrixNeighbors,distanceMatrixNeighbors,graphSupportedDistanceIndices,distanceMatrixIndex,hs]

theorem sourceRetainedDistance_original_sum (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (N a n : ℕ) (sig t θ v : ℝ) (hθ : θ = graphUncappedAngularScale N sig t)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (β γ : Plane → UnitCircle → ℂ) (Ψ : ℝ → ℝ)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) :
    let axis := sourceParentAxis (Q₁.descendant A) (Q₂.descendant B)
    let I := graphRetainedIndices
      (sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
      N sig (a+n) true ![Q₁,Q₂,Q₂,Q₁] rep
    let H := graphSupportedDistanceIndices
      (sourceRetainedDistanceIndices Q₁ Q₂ ρ ν β γ A B a n N sig t θ rep) θ axis
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ![ρ,ν,ν,ρ]
      (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier) ![M₁,M₂,M₂,M₁] ![β,γ,γ,β]
      true e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ
    (∑ e ∈ I, F e) = ∑ e ∈ H, F e := by
  classical
  dsimp only
  let I := graphRetainedIndices
    (sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    N sig ((a:ℝ)+n) true ![Q₁,Q₂,Q₂,Q₁] rep
  have he := graphOriginalDistanceSum_eligible Q₁ Q₂ A B N n sig t θ v hθ ρ ν M₁ M₂ β γ Ψ I
    (Finset.filter_subset _ _)
  exact he.trans (graphOriginalDistanceSum_supported _ _ _ _ _ _ _ _ _)

end PlanarFalconer

end OAI

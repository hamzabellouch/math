import OAI.MeasureTheory.Falconer.Graphs.EligibleDistanceGraphSum
import OAI.MeasureTheory.Falconer.Graphs.ParentGraphIndices
import OAI.MeasureTheory.Falconer.Graphs.GraphRetainedEdges

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def distanceSlotBin (j k : ℕ) (l : Fin 4) : ℕ := ![j,j,k,k] l

def GraphDistanceIndexEligible (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (β γ : Plane → UnitCircle → ℂ) (m : ℕ) (axis : ℝ) (e : GraphNonedgeIndex) : Prop :=
  ∀ l : Fin 4, RotatedAngularLabelEligible (![ρ,ν,ν,ρ] l)
    (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier (![β,γ,γ,β] l)
    m (distanceSlotBin e.2.1.1 e.2.1.2 l) axis

noncomputable def graphDistanceEligibleIndices (I : Finset GraphNonedgeIndex)
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (m : ℕ) (axis : ℝ) : Finset GraphNonedgeIndex := by
  classical
  exact I.filter (GraphDistanceIndexEligible Q₁ Q₂ ρ ν β γ m axis)

theorem sourceParentGraphIndex_eligible_iff (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (N : ℕ) (sig t : ℝ) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (e f : ParentDistanceBinLabel) :
    GraphDistanceIndexEligible Q₁ Q₂ ρ ν β γ (angularBinCount (graphUncappedAngularScale N sig t))
      (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B)) (sourceParentGraphIndex A B (e,f)) ↔
    SourceParentBinEligible N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν β γ e ∧
    SourceParentBinEligible N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν β γ f := by
  simp [GraphDistanceIndexEligible,SourceParentBinEligible,Fin.forall_fin_succ,
    graphQuadCells,graphQuadPath,sourceParentGraphIndex,distanceSlotBin,DyadicSquare.descendant_append,and_comm,and_left_comm,and_assoc]

theorem sourceParentGraphIndex_original_term (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (N : ℕ) (sig t v : ℝ) (ρ ν : Measure Plane) (M₁ M₂ : ℝ)
    (β γ : Plane → UnitCircle → ℂ) (Ψ : ℝ → ℝ) (e f : ParentDistanceBinLabel) :
    graphOriginalTerm ![ρ,ν,ν,ρ]
      (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] (sourceParentGraphIndex A B (e,f)).1 l).carrier)
      ![M₁,M₂,M₂,M₁] ![β,γ,γ,β] true (sourceParentGraphIndex A B (e,f)).2.2
      (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B)) (graphUncappedAngularScale N sig t) v
      (sourceParentGraphIndex A B (e,f)).2.1.1 (sourceParentGraphIndex A B (e,f)).2.1.2 Ψ =
    sourceParentGraphTerm N sig t v (Q₁.descendant A) (Q₂.descendant B) ρ ν M₁ M₂ β γ Ψ e f := by
  unfold sourceParentGraphTerm
  simp only [sourceParentGraphIndex_cells]
  congr 1
  funext l
  fin_cases l <;> rfl

theorem graphOriginalDistanceSum_eligible (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (N n : ℕ) (sig t θ v : ℝ) (hθ : θ = graphUncappedAngularScale N sig t)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (β γ : Plane → UnitCircle → ℂ) (Ψ : ℝ → ℝ)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B) :
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ![ρ,ν,ν,ρ]
      (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier) ![M₁,M₂,M₂,M₁] ![β,γ,γ,β]
      true e.2.2 (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B)) θ v e.2.1.1 e.2.1.2 Ψ
    (∑ e ∈ I, F e) = ∑ e ∈ graphDistanceEligibleIndices I Q₁ Q₂ ρ ν β γ (angularBinCount θ)
      (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B)), F e := by
  classical
  subst θ
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hn
  have hnot : ¬GraphDistanceIndexEligible Q₁ Q₂ ρ ν β γ (angularBinCount (graphUncappedAngularScale N sig t))
      (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B)) e := by
    intro hh
    exact hn (Finset.mem_filter.mpr ⟨he,hh⟩)
  obtain ⟨⟨e,f⟩,_,rfl⟩ := Finset.mem_image.mp (hI he)
  rw [sourceParentGraphIndex_eligible_iff] at hnot
  rw [sourceParentGraphIndex_original_term]
  exact sourceParentGraphTerm_zero_of_ineligible N sig t v (Q₁.descendant A) (Q₂.descendant B)
    ρ ν M₁ M₂ β γ Ψ e f (not_and_or.mp hnot)

end PlanarFalconer

end OAI

import OAI.MeasureTheory.Falconer.Estimates.SelectedDistanceAssembly

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

abbrev ParentDistanceBinLabel := Σ _ : CellPath × CellPath, ℕ

noncomputable def sourceParentBinLabels (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (n : ℕ) : Finset ParentDistanceBinLabel :=
  ((occupiedAnchorPaths X ρ n) ×ˢ (occupiedAnchorPaths Y ν n)).sigma
    (fun AB => sourceParentActiveLabels N sig t X Y AB.1 AB.2)

noncomputable def sourceParentBinIntegrand (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (e : ParentDistanceBinLabel) : ℝ × UnitCircle → ℂ :=
  distanceBinIntegrand ρ ν (X.descendant e.1.1).carrier (Y.descendant e.1.2).carrier
    M₁ M₂ b₁ b₂ (sourceParentAxis X Y) (angularBinCount (graphUncappedAngularScale N sig t)) e.2

theorem sourceParentRetainedF_bin_sum (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) :
    sourceParentRetainedF N sig t X Y ρ ν n M₁ M₂ b₁ b₂ r =
      ∑ e ∈ sourceParentBinLabels N sig t X Y ρ ν n,
        ∫ u, sourceParentBinIntegrand N sig t X Y ρ ν M₁ M₂ b₁ b₂ e (r,u) ∂sourceArcLength := by
  simp only [sourceParentRetainedF,sourceCellwiseDistanceF,sourceParentRetainedSelection_eq_bins,
    sourceParentBinLabels,Finset.sum_sigma,Finset.sum_product,sourceParentBinIntegrand]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  exact sourceDistanceF_selected_bins ρ ν _ _ hM₁ hM₂ b₁ b₂ h₁ h₂ hB₁ hB₂ hb₁ hb₂ _ _ _ r

theorem sourceParentBinLabels_spec {N n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {e : ParentDistanceBinLabel}
    (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    e.1.1 ∈ occupiedAnchorPaths X ρ n ∧ e.1.2 ∈ occupiedAnchorPaths Y ν n ∧
      e.2 ∈ sourceParentActiveLabels N sig t X Y e.1.1 e.1.2 := by
  rcases Finset.mem_sigma.mp he with ⟨hpaths, hbin⟩
  exact ⟨(Finset.mem_product.mp hpaths).1, (Finset.mem_product.mp hpaths).2, hbin⟩

theorem sourceParentBinLabels_length {N n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {e : ParentDistanceBinLabel}
    (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    e.1.1.length = n ∧ e.1.2.length = n := by
  obtain ⟨hA,hB,_⟩ := sourceParentBinLabels_spec he
  exact ⟨(mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hA).1,
    (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hB).1⟩

theorem sourceParentBinLabels_bin_lt {N n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {e : ParentDistanceBinLabel}
    (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    e.2 < angularBinCount (graphUncappedAngularScale N sig t) :=
  Finset.mem_range.mp (Finset.mem_sdiff.mp (sourceParentBinLabels_spec he).2.2).1

end PlanarFalconer

end OAI

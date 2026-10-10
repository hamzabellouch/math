import OAI.MeasureTheory.Falconer.Angular.RotatedGraphEligibility
import OAI.MeasureTheory.Falconer.Graphs.ParentGraphEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem sourceParentGraphTerm_zero_of_ineligible (N : ℕ) (sig t v : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (Ψ : ℝ → ℝ) (e f : ParentDistanceBinLabel)
    (he : ¬SourceParentBinEligible N sig t X Y ρ ν b₁ b₂ e ∨
      ¬SourceParentBinEligible N sig t X Y ρ ν b₁ b₂ f) :
    sourceParentGraphTerm N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f = 0 := by
  simp only [sourceParentGraphTerm,graphOriginalTerm,← distanceBinIntegrand_cross]
  change ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
    (sourceParentBinIntegrand N sig t X Y ρ ν M₁ M₂ b₁ b₂ e (r,u) *
      conj (sourceParentBinIntegrand N sig t X Y ρ ν M₁ M₂ b₁ b₂ f (r,w)))
      ∂sourceArcLength ∂sourceArcLength) = 0
  rcases he with he | hf
  · simp only [sourceParentBinIntegrand_zero_of_ineligible N sig t X Y ρ ν M₁ M₂ b₁ b₂ e he,
      zero_mul,smul_zero,integral_zero]
  · simp only [sourceParentBinIntegrand_zero_of_ineligible N sig t X Y ρ ν M₁ M₂ b₁ b₂ f hf,
      map_zero,mul_zero,smul_zero,integral_zero]

theorem sourceParentGraphSum_eligible (N n : ℕ) (sig t v : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (Ψ : ℝ → ℝ) :
    (∑ e ∈ sourceParentBinLabels N sig t X Y ρ ν n,
      ∑ f ∈ sourceParentBinLabels N sig t X Y ρ ν n,
        sourceParentGraphTerm N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f) =
    ∑ e ∈ sourceParentEligibleBinLabels N sig t X Y ρ ν n b₁ b₂,
      ∑ f ∈ sourceParentEligibleBinLabels N sig t X Y ρ ν n b₁ b₂,
        sourceParentGraphTerm N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f := by
  classical
  let S := sourceParentBinLabels N sig t X Y ρ ν n
  let E := sourceParentEligibleBinLabels N sig t X Y ρ ν n b₁ b₂
  have hsub : E ⊆ S := Finset.filter_subset _ _
  have hn : ∀ e ∈ S, e ∉ E → ¬SourceParentBinEligible N sig t X Y ρ ν b₁ b₂ e := by
    intro e he hnot hyes
    exact hnot (Finset.mem_filter.mpr ⟨he,hyes⟩)
  let F := sourceParentGraphTerm N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ
  change (∑ e ∈ S, ∑ f ∈ S, F e f) = ∑ e ∈ E, ∑ f ∈ E, F e f
  calc
    _ = ∑ e ∈ E, ∑ f ∈ S, F e f := by
      symm
      apply Finset.sum_subset hsub
      intro e he hnot
      apply Finset.sum_eq_zero
      intro f _
      exact sourceParentGraphTerm_zero_of_ineligible N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f
        (Or.inl (hn e he hnot))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      symm
      apply Finset.sum_subset hsub
      intro f hf hnot
      exact sourceParentGraphTerm_zero_of_ineligible N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f
        (Or.inr (hn f hf hnot))

theorem sourceParentGraph_filtered_sum_eligible (N n : ℕ) (sig t v : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (Ψ : ℝ → ℝ)
    (keep : ParentDistanceBinLabel → ParentDistanceBinLabel → Prop) [DecidableRel keep] :
    (∑ e ∈ sourceParentBinLabels N sig t X Y ρ ν n,
      ∑ f ∈ sourceParentBinLabels N sig t X Y ρ ν n,
        if keep e f then sourceParentGraphTerm N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f else 0) =
    ∑ e ∈ sourceParentEligibleBinLabels N sig t X Y ρ ν n b₁ b₂,
      ∑ f ∈ sourceParentEligibleBinLabels N sig t X Y ρ ν n b₁ b₂,
        if keep e f then sourceParentGraphTerm N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f else 0 := by
  classical
  let S := sourceParentBinLabels N sig t X Y ρ ν n
  let E := sourceParentEligibleBinLabels N sig t X Y ρ ν n b₁ b₂
  have hsub : E ⊆ S := Finset.filter_subset _ _
  have hn : ∀ e ∈ S, e ∉ E → ¬SourceParentBinEligible N sig t X Y ρ ν b₁ b₂ e := by
    intro e he hnot hyes
    exact hnot (Finset.mem_filter.mpr ⟨he,hyes⟩)
  let F := fun e f => if keep e f then sourceParentGraphTerm N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f else 0
  have hzero (e f : ParentDistanceBinLabel)
      (hh : ¬SourceParentBinEligible N sig t X Y ρ ν b₁ b₂ e ∨
        ¬SourceParentBinEligible N sig t X Y ρ ν b₁ b₂ f) : F e f = 0 := by
    simp only [F,sourceParentGraphTerm_zero_of_ineligible N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f hh,ite_self]
  change (∑ e ∈ S, ∑ f ∈ S, F e f) = ∑ e ∈ E, ∑ f ∈ E, F e f
  calc
    _ = ∑ e ∈ E, ∑ f ∈ S, F e f := by
      symm
      apply Finset.sum_subset hsub
      intro e he hnot
      exact Finset.sum_eq_zero (fun f _ => hzero e f (Or.inl (hn e he hnot)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      symm
      apply Finset.sum_subset hsub
      intro f hf hnot
      exact hzero e f (Or.inr (hn f hf hnot))

theorem sourceParentEligibleBin_witnesses (N n : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (b₁ b₂ : Plane → UnitCircle → ℂ)
    {e : ParentDistanceBinLabel} (he : e ∈ sourceParentEligibleBinLabels N sig t X Y ρ ν n b₁ b₂)
    (G₁ G₂ : Plane → UnitCircle → Prop)
    (hG₁ : ∀ dir, ∀ᵐ x ∂ρ.restrict (X.descendant e.1.1).carrier, b₁ x dir ≠ 0 → G₁ x dir)
    (hG₂ : ∀ dir, ∀ᵐ x ∂ν.restrict (Y.descendant e.1.2).carrier, b₂ x dir ≠ 0 → G₂ x dir) :
    (∃ dir, sourceCircleRotate (-(sourceParentAxis X Y)) dir ∈
      tsupport (circleAngularBin (angularBinCount (graphUncappedAngularScale N sig t)) e.2) ∧
      ∃ x ∈ (X.descendant e.1.1).carrier, b₁ x dir ≠ 0 ∧ G₁ x dir) ∧
    (∃ dir, sourceCircleRotate (-(sourceParentAxis X Y)) dir ∈
      tsupport (circleAngularBin (angularBinCount (graphUncappedAngularScale N sig t)) e.2) ∧
      ∃ y ∈ (Y.descendant e.1.2).carrier, b₂ y dir ≠ 0 ∧ G₂ y dir) := by
  classical
  have hel := (Finset.mem_filter.mp he).2
  exact ⟨rotated_eligible_label_witness (X.descendant e.1.1).measurable hel.1 G₁ hG₁,
    rotated_eligible_label_witness (Y.descendant e.1.2).measurable hel.2 G₂ hG₂⟩

end PlanarFalconer

end OAI

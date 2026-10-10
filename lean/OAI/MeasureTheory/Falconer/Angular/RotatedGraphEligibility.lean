import OAI.MeasureTheory.Falconer.Angular.AngularLabelEligibility
import OAI.MeasureTheory.Falconer.Recursion.ParentBinFamily

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

def RotatedAngularLabelEligible (ρ : Measure Plane) (X : Set Plane)
    (b : Plane → UnitCircle → ℂ) (n j : ℕ) (axis : ℝ) : Prop :=
  AngularLabelEligible ρ X (fun x u => b x (sourceCircleRotate axis u)) n j

theorem rotated_ineligible_transform_zero {ρ : Measure Plane} {X : Set Plane}
    {b : Plane → UnitCircle → ℂ} {n j : ℕ} {axis : ℝ}
    (h : ¬RotatedAngularLabelEligible ρ X b n j axis) (M r : ℝ) (dir : UnitCircle) :
    rotatedBinSelection n {j} axis dir * sourceAngularTransform ρ X M b r dir = 0 := by
  have hrot : sourceCircleRotate axis (sourceCircleRotate (-axis) dir) = dir := by
    simp only [sourceCircleRotate_add,neg_add_cancel,sourceCircleRotate_zero]
  by_cases hz : circleAngularBin n j (sourceCircleRotate (-axis) dir) = 0
  · simp [rotatedBinSelection,hz]
  · have he := ineligible_symbol_zero_ae h (subset_closure hz)
    simp only [hrot] at he
    have hi : (∫ x in X, Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (dir : Plane) x : ℂ))*b x dir ∂ρ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [he] with x hx
      simp [hx]
    simp only [sourceAngularTransform,hi,smul_zero,mul_zero]

theorem rotated_eligible_label_witness {ρ : Measure Plane} {X : Set Plane}
    (hX : MeasurableSet X) {b : Plane → UnitCircle → ℂ} {n j : ℕ} {axis : ℝ}
    (h : RotatedAngularLabelEligible ρ X b n j axis) (G : Plane → UnitCircle → Prop)
    (hG : ∀ dir, ∀ᵐ x ∂ρ.restrict X, b x dir ≠ 0 → G x dir) :
    ∃ dir, sourceCircleRotate (-axis) dir ∈ tsupport (circleAngularBin n j) ∧
      ∃ x ∈ X, b x dir ≠ 0 ∧ G x dir := by
  obtain ⟨u,hu,x,hx,hb,hgood⟩ := eligible_label_witness hX h
    (fun x u => G x (sourceCircleRotate axis u)) (fun u => hG _)
  refine ⟨sourceCircleRotate axis u,?_,x,hx,hb,hgood⟩
  simpa only [sourceCircleRotate_add,add_neg_cancel,sourceCircleRotate_zero] using hu

def SourceParentBinEligible (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (b₁ b₂ : Plane → UnitCircle → ℂ) (e : ParentDistanceBinLabel) : Prop :=
  RotatedAngularLabelEligible ρ (X.descendant e.1.1).carrier b₁
    (angularBinCount (graphUncappedAngularScale N sig t)) e.2 (sourceParentAxis X Y) ∧
  RotatedAngularLabelEligible ν (Y.descendant e.1.2).carrier b₂
    (angularBinCount (graphUncappedAngularScale N sig t)) e.2 (sourceParentAxis X Y)

noncomputable def sourceParentEligibleBinLabels (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (n : ℕ) (b₁ b₂ : Plane → UnitCircle → ℂ) : Finset ParentDistanceBinLabel := by
  classical
  exact (sourceParentBinLabels N sig t X Y ρ ν n).filter (SourceParentBinEligible N sig t X Y ρ ν b₁ b₂)

theorem sourceParentBinIntegrand_zero_of_ineligible (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (e : ParentDistanceBinLabel)
    (he : ¬SourceParentBinEligible N sig t X Y ρ ν b₁ b₂ e) (z : ℝ × UnitCircle) :
    sourceParentBinIntegrand N sig t X Y ρ ν M₁ M₂ b₁ b₂ e z = 0 := by
  classical
  unfold SourceParentBinEligible at he
  push Not at he
  by_cases h₁ : RotatedAngularLabelEligible ρ (X.descendant e.1.1).carrier b₁
      (angularBinCount (graphUncappedAngularScale N sig t)) e.2 (sourceParentAxis X Y)
  · have hz := rotated_ineligible_transform_zero (he h₁) M₂ z.1 z.2
    rcases mul_eq_zero.mp hz with hb | hv
    · simp [sourceParentBinIntegrand,distanceBinIntegrand,hb]
    · simp [sourceParentBinIntegrand,distanceBinIntegrand,hv]
  · have hz := rotated_ineligible_transform_zero h₁ M₁ z.1 z.2
    rcases mul_eq_zero.mp hz with hb | hu
    · simp [sourceParentBinIntegrand,distanceBinIntegrand,hb]
    · simp [sourceParentBinIntegrand,distanceBinIntegrand,hu]

theorem sourceParentBin_integral_sum_eligible (N n : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) :
    (∑ e ∈ sourceParentBinLabels N sig t X Y ρ ν n,
      ∫ u, sourceParentBinIntegrand N sig t X Y ρ ν M₁ M₂ b₁ b₂ e (r,u) ∂sourceArcLength) =
    ∑ e ∈ sourceParentEligibleBinLabels N sig t X Y ρ ν n b₁ b₂,
      ∫ u, sourceParentBinIntegrand N sig t X Y ρ ν M₁ M₂ b₁ b₂ e (r,u) ∂sourceArcLength := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hnot
  have hn : ¬SourceParentBinEligible N sig t X Y ρ ν b₁ b₂ e := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨he,h⟩)
  simp only [sourceParentBinIntegrand_zero_of_ineligible N sig t X Y ρ ν M₁ M₂ b₁ b₂ e hn,integral_zero]

end PlanarFalconer

end OAI

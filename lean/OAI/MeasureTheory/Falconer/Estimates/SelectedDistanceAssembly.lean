import OAI.MeasureTheory.Falconer.Graphs.ParentRetainedEnergy
import OAI.MeasureTheory.Falconer.Angular.GraphRotatedWeights
import OAI.MeasureTheory.Falconer.Angular.FiniteAngularSquare

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def distanceBinIntegrand (ρ ν : Measure Plane) (X Y : Set Plane)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (axis : ℝ) (n j : ℕ)
    (z : ℝ × UnitCircle) : ℂ :=
  (sourceConeCircle axis z.2 * rotatedBinSelection n {j} axis z.2) *
    sourceAngularTransform ρ X M₁ b₁ z.1 z.2 *
      conj (sourceAngularTransform ν Y M₂ b₂ z.1 z.2)

theorem distanceBinIntegrand_measurable (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) (axis : ℝ) (n j : ℕ) :
    Measurable (distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j) := by
  exact (((measurable_sourceConeCircle axis).comp measurable_snd |>.mul
    ((measurable_rotatedBinSelection n {j} axis).comp measurable_snd)).mul
    (measurable_sourceAngularTransform ρ X M₁ b₁ h₁)).mul
    (Complex.continuous_conj.measurable.comp (measurable_sourceAngularTransform ν Y M₂ b₂ h₂))

theorem distanceBinIntegrand_bound (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b₁ b₂ : Plane → UnitCircle → ℂ) {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    (axis : ℝ) (n j : ℕ) (z : ℝ × UnitCircle) :
    ‖distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j z‖ ≤
      (B₁*(ρ X).toReal/M₁)*(B₂*(ν Y).toReal/M₂) := by
  have hw : ‖sourceConeCircle axis z.2 * rotatedBinSelection n {j} axis z.2‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (sourceConeCircle_norm_le axis z.2)
      (rotatedBinSelection_norm_le n {j} axis z.2) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  rw [distanceBinIntegrand, norm_mul, norm_mul, Complex.norm_conj]
  exact (mul_le_mul (mul_le_mul hw (sourceAngularTransform_norm_le ρ X M₁ hM₁ b₁ B₁
    (fun x _ => hb₁ x) z.1 z.2) (norm_nonneg _) (by norm_num))
    (sourceAngularTransform_norm_le ν Y M₂ hM₂ b₂ B₂ (fun y _ => hb₂ y) z.1 z.2)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem sourceDistanceF_selected_bins (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    (axis : ℝ) (n : ℕ) (S : Finset ℕ) (r : ℝ) :
    sourceDistanceF (fun dir => sourceConeCircle axis dir * rotatedBinSelection n S axis dir)
      (fun z => sourceAngularTransform ρ X M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ b₂ z.1 z.2) r =
      ∑ j ∈ S, ∫ u, distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j (r,u) ∂sourceArcLength := by
  have he (u : UnitCircle) :
      sourceConeCircle axis u * rotatedBinSelection n S axis u * sourceAngularTransform ρ X M₁ b₁ r u *
        conj (sourceAngularTransform ν Y M₂ b₂ r u) =
      ∑ j ∈ S, distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j (r,u) := by
    simp only [distanceBinIntegrand, rotatedBinSelection, Finset.sum_singleton, Complex.ofReal_sum,
      Finset.mul_sum, Finset.sum_mul]
  simp only [sourceDistanceF, he]
  apply integral_finsetSum
  intro j _
  exact Integrable.of_bound
    ((distanceBinIntegrand_measurable ρ ν X Y M₁ M₂ b₁ b₂ h₁ h₂ axis n j).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable _
    (Filter.Eventually.of_forall (fun u => distanceBinIntegrand_bound ρ ν X Y hM₁ hM₂ b₁ b₂
      hB₁ hB₂ hb₁ hb₂ axis n j (r,u)))

noncomputable def sourceParentActiveLabels (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (A B : CellPath) : Finset ℕ :=
  Finset.range (angularBinCount (graphUncappedAngularScale N sig t)) \
    inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t))
      (sourceCenteredCellDirection X Y (X.descendant A) (Y.descendant B))
      (3*graphUncappedAngularScale N sig t)

theorem sourceParentRetainedSelection_eq_bins (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (A B : CellPath) (dir : UnitCircle) :
    1-sourceParentInactiveSelection N sig t X Y A B dir =
      rotatedBinSelection (angularBinCount (graphUncappedAngularScale N sig t))
        (sourceParentActiveLabels N sig t X Y A B) (sourceParentAxis X Y) dir := by
  exact (inactive_rotated_complement _ (angularBinCount_pos (by unfold graphUncappedAngularScale; positivity))
    _ _ _ _).symm

end PlanarFalconer

end OAI

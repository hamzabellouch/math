import OAI.MeasureTheory.Falconer.Recursion.ParentBinSelection
import OAI.MeasureTheory.Falconer.Geometry.CellwiseDistanceForm
import OAI.MeasureTheory.Falconer.Radial.RadialDistanceError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceParentDistanceF (X Y : DyadicSquare) (ρ ν : Measure Plane)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) : ℝ → ℂ :=
  sourceDistanceF (sourceConeCircle (sourceParentAxis X Y))
    (fun z => sourceAngularTransform ρ X.carrier M₁ b₁ z.1 z.2)
    (fun z => sourceAngularTransform ν Y.carrier M₂ b₂ z.1 z.2)

noncomputable def sourceParentDiscardedF (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (ρ ν : Measure Plane) (n : ℕ)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) : ℝ → ℂ :=
  sourceCellwiseDistanceF X Y ρ ν n n M₁ M₂
    (fun A B dir => sourceConeCircle (sourceParentAxis X Y) dir *
      sourceParentInactiveSelection N sig t X Y A B dir) b₁ b₂

noncomputable def sourceParentRetainedF (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (ρ ν : Measure Plane) (n : ℕ)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) : ℝ → ℂ :=
  sourceCellwiseDistanceF X Y ρ ν n n M₁ M₂
    (fun A B dir => sourceConeCircle (sourceParentAxis X Y) dir *
      (1-sourceParentInactiveSelection N sig t X Y A B dir)) b₁ b₂

theorem sourceAngularShellMeasure_ae_nonzero (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) :
    ∀ᵐ r ∂sourceAngularShellMeasure v Ψ, Ψ (r/(2:ℝ)^v) ≠ 0 := by
  unfold sourceAngularShellMeasure
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards with r hr
  intro hz
  apply hr
  simp only [hz, zero_div, ENNReal.ofReal_zero]

theorem sourceParentF_partition (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (hX : 0 < X.side) (hY : 0 < Y.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) :
    sourceParentDistanceF X Y ρ ν M₁ M₂ b₁ b₂ r =
      sourceParentRetainedF N sig t X Y ρ ν n M₁ M₂ b₁ b₂ r +
      sourceParentDiscardedF N sig t X Y ρ ν n M₁ M₂ b₁ b₂ r :=
  sourceCellwiseDistanceF_partition X Y hX hY ρ ν n n hM₁ hM₂ _ _ b₁ b₂
    (measurable_sourceConeCircle _) (sourceParentInactiveSelection_measurable _ _ _ _ _)
    h₁ h₂ (by norm_num) hB₁ hB₂ (sourceConeCircle_norm_le _)
    (sourceParentInactiveSelection_norm_le _ _ _ _ _) hb₁ hb₂ r

theorem sourceParentRetainedF_measurable (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (n : ℕ) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) :
    Measurable (sourceParentRetainedF N sig t X Y ρ ν n M₁ M₂ b₁ b₂) :=
  measurable_sourceCellwiseDistanceF X Y ρ ν n n M₁ M₂ _ _ _
    (fun A B => (measurable_sourceConeCircle _).mul
      (measurable_const.sub (sourceParentInactiveSelection_measurable _ _ _ _ _ A B))) h₁ h₂

theorem sourceParentDistanceF_measurable (X Y : DyadicSquare) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) :
    Measurable (sourceParentDistanceF X Y ρ ν M₁ M₂ b₁ b₂) :=
  measurable_sourceDistanceF _ _ _ (measurable_sourceConeCircle _)
    (measurable_sourceAngularTransform ρ _ _ b₁ h₁)
    (measurable_sourceAngularTransform ν _ _ b₂ h₂)

theorem parent_retained_energy_error_le (N : ℕ) (sig t a v : ℝ)
    (X Y : DyadicSquare) (hX : 0 < X.side) (hY : 0 < Y.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) {W : ℝ} (hW : 0 ≤ W)
    (hΨW : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hfull : ∀ r, ‖sourceParentDistanceF X Y ρ ν M₁ M₂ b₁ b₂ r‖ ≤ C)
    (he : ∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
      ‖sourceParentDiscardedF N sig t X Y ρ ν n M₁ M₂ b₁ b₂ r‖ ≤ ε) :
    |sourceRadialSquareEnergy a v Ψ (sourceParentDistanceF X Y ρ ν M₁ M₂ b₁ b₂) -
      sourceRadialSquareEnergy a v Ψ (sourceParentRetainedF N sig t X Y ρ ν n M₁ M₂ b₁ b₂)| ≤
      (2:ℝ)^(2*(v-a)) * (2*C*ε+ε^2) * (4*W) := by
  rw [abs_sub_comm]
  apply sourceRadialSquareEnergy_error_le a v Ψ hW hΨW hs _ _
    (sourceParentRetainedF_measurable N sig t X Y ρ ν n M₁ M₂ b₁ b₂ h₁ h₂)
    (sourceParentDistanceF_measurable X Y ρ ν M₁ M₂ b₁ b₂ h₁ h₂) hC hε
    (Filter.Eventually.of_forall hfull)
  filter_upwards [sourceAngularShellMeasure_ae_nonzero v Ψ hΨ] with r hr
  rw [sourceParentF_partition N sig t X Y hX hY ρ ν n hM₁ hM₂ b₁ b₂ h₁ h₂ hB₁ hB₂ hb₁ hb₂,
    sub_add_cancel_left, norm_neg]
  exact he r hr

end PlanarFalconer

end OAI

import OAI.MeasureTheory.Falconer.Graphs.ParentRetainedEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def sourceParentHF (a v : ℝ) (Ψ : ℝ → ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) : ℝ≥0∞ :=
  sourceDistanceHF a v Ψ (sourceConeCircle (sourceParentAxis X Y))
    (fun z => sourceAngularTransform ρ X.carrier M₁ b₁ z.1 z.2)
    (fun z => sourceAngularTransform ν Y.carrier M₂ b₂ z.1 z.2)

theorem sourceParentHF_finite_eq (a v : ℝ) (Ψ : ℝ → ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ W : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hW : 0 ≤ W)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    (hΨW : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceParentHF a v Ψ X Y ρ ν M₁ M₂ b₁ b₂ ≠ ⊤ ∧
      (sourceParentHF a v Ψ X Y ρ ν M₁ M₂ b₁ b₂).toReal =
        sourceRadialSquareEnergy a v Ψ (sourceParentDistanceF X Y ρ ν M₁ M₂ b₁ b₂) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hΨW hs
  have hh := sourceDistanceHF_eq_ofReal a v Ψ (sourceConeCircle (sourceParentAxis X Y)) _ _
    (sourceParentDistanceF_measurable X Y ρ ν M₁ M₂ b₁ b₂ h₁ h₂)
    (show 0 ≤ (1*B₁*B₂*sourceArcLength.real univ)*((ρ X.carrier).toReal/M₁)*((ν Y.carrier).toReal/M₂) by positivity)
    (Filter.Eventually.of_forall (sourceDistanceF_norm_le ρ ν X.carrier Y.carrier hM₁ hM₂
      _ b₁ b₂ (by norm_num) hB₁ hB₂ (sourceConeCircle_norm_le _) (fun x _ => hb₁ x) (fun y _ => hb₂ y)))
  change sourceParentHF a v Ψ X Y ρ ν M₁ M₂ b₁ b₂ =
    ENNReal.ofReal (sourceRadialSquareEnergy a v Ψ (sourceParentDistanceF X Y ρ ν M₁ M₂ b₁ b₂)) at hh
  rw [hh]
  refine ⟨ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ?_⟩
  unfold sourceRadialSquareEnergy
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (integral_nonneg (fun _ => sq_nonneg _))

end PlanarFalconer

end OAI

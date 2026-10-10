import OAI.MeasureTheory.Falconer.Angular.AngularCellKernels
import OAI.MeasureTheory.Falconer.Angular.AngularOccupiedPartition

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem sourceAngularH_kernel (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) = angularKernelIntegral a v Ψ
      (fun z => (U (z.1,z.2.1)*conj (U (z.1,z.2.1)))*(V (z.1,z.2.2)*conj (V (z.1,z.2.2)))) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  have hz : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  have hm : Measurable (fun z : ℝ × (UnitCircle × UnitCircle) =>
      (U (z.1,z.2.1)*conj (U (z.1,z.2.1)))*(V (z.1,z.2.2)*conj (V (z.1,z.2.2)))) := by
    fun_prop
  have hb (z : ℝ × (UnitCircle × UnitCircle)) :
      ‖(U (z.1,z.2.1)*conj (U (z.1,z.2.1)))*(V (z.1,z.2.2)*conj (V (z.1,z.2.2)))‖ ≤ C^2*D^2 := by
    simp only [norm_mul,Complex.norm_conj,← pow_two]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hbU _) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hbV _) 2) (sq_nonneg _) (sq_nonneg _)
  rw [angularKernelIntegral_original a v hΨ hpos hz _ hm hb]
  exact sourceAngularH_complex_integral a v hΨ hpos hs hW hw U V hU hV hC hD hbU hbV

theorem angular_parent_near_far
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (A B : CellPath) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (n : ℕ) (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    {Ma₁ Ma₂ Mp₁ Mp₂ : ℝ} (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) :
    let U := angularCellTransform Q₁ ρ Ma₁ β A
    let V := angularCellTransform Q₂ ν Ma₂ γ B
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) =
      angularCellContribution Q₁ Q₂ ρ ν A B n a v Ψ Ma₁ Ma₂ Mp₁ Mp₂ β γ G +
      angularCellContribution Q₁ Q₂ ρ ν A B n a v Ψ Ma₁ Ma₂ Mp₁ Mp₂ β γ (fun row col => ¬ G row col) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  let U := angularCellTransform Q₁ ρ Ma₁ β A
  let V := angularCellTransform Q₂ ν Ma₂ γ B
  have hu := angularCellTransform_measurable Q₁ ρ Ma₁ β hβ A
  have hv := angularCellTransform_measurable Q₂ ν Ma₂ γ hγ B
  have hbu := fun z : ℝ × UnitCircle =>
    sourceAngularTransform_global_bound ρ (Q₁.descendant A).carrier hMa₁ β hD₁ hbβ z.1 z.2
  have hbv := fun z : ℝ × UnitCircle =>
    sourceAngularTransform_global_bound ν (Q₂.descendant B).carrier hMa₂ γ hD₂ hbγ z.1 z.2
  have hh := sourceAngularH_kernel a v hΨ hpos hs hW hw U V hu hv
    (C := D₁*(ρ univ).toReal/Ma₁) (D := D₂*(ν univ).toReal/Ma₂) (by positivity) (by positivity) hbu hbv
  refine ⟨hh.1,hh.2.trans ?_⟩
  let C := sourceProductVertices Q₁ Q₂ ρ ν A B n
  let Uc := angularCellTransform Q₁ ρ Mp₁ β
  let Vc := angularCellTransform Q₂ ν Mp₂ γ
  have hsplit := angularRestrictedIntegral_complement a v Ψ C G Uc Vc
    (angularCellTransform_measurable Q₁ ρ Mp₁ β hβ)
    (angularCellTransform_measurable Q₂ ν Mp₂ γ hγ)
    (B := D₁*(ρ univ).toReal/Mp₁) (D := D₂*(ν univ).toReal/Mp₂) (by positivity) (by positivity)
    (fun P z => sourceAngularTransform_global_bound ρ _ hMp₁ β hD₁ hbβ z.1 z.2)
    (fun P z => sourceAngularTransform_global_bound ν _ hMp₂ γ hD₂ hbγ z.1 z.2)
  unfold angularCellContribution
  rw [← smul_add,hsplit,← angularKernelIntegral_smul]
  congr 1
  funext z
  exact angular_parent_occupied_partition Q₁ Q₂ hQ₁ hQ₂ A B ρ ν n Ma₁ Ma₂ Mp₁ Mp₂
    hMp₁.ne' hMp₂.ne' β γ hβ hγ D₁ D₂ hbβ hbγ z.1 z.2.1 z.2.2

end PlanarFalconer

end OAI

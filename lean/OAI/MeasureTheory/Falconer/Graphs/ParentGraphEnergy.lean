import OAI.MeasureTheory.Falconer.Recursion.ParentBinFamily
import OAI.MeasureTheory.Falconer.Graphs.DistanceGraphCross
import OAI.MeasureTheory.Falconer.Shells.OriginalShellIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceParentGraphTerm (N : ℕ) (sig t v : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (Ψ : ℝ → ℝ) (e f : ParentDistanceBinLabel) : ℂ :=
  graphOriginalTerm ![ρ,ν,ν,ρ]
    ![(X.descendant e.1.1).carrier,(Y.descendant e.1.2).carrier,
      (Y.descendant f.1.2).carrier,(X.descendant f.1.1).carrier]
    ![M₁,M₂,M₂,M₁] ![b₁,b₂,b₂,b₁] true true (sourceParentAxis X Y)
    (graphUncappedAngularScale N sig t) v e.2 f.2 Ψ

theorem sourceParentRetainedEnergy_graph_sum (N : ℕ) (sig t a v : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W) :
    (sourceRadialSquareEnergy a v Ψ (sourceParentRetainedF N sig t X Y ρ ν n M₁ M₂ b₁ b₂) : ℂ) =
      ((2:ℝ)^(2*(v-a))) •
        ∑ e ∈ sourceParentBinLabels N sig t X Y ρ ν n,
        ∑ f ∈ sourceParentBinLabels N sig t X Y ρ ν n,
          sourceParentGraphTerm N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f := by
  let S := sourceParentBinLabels N sig t X Y ρ ν n
  let F := sourceParentBinIntegrand N sig t X Y ρ ν M₁ M₂ b₁ b₂
  let C := fun e : ParentDistanceBinLabel =>
    (B₁*(ρ (X.descendant e.1.1).carrier).toReal/M₁)*
      (B₂*(ν (Y.descendant e.1.2).carrier).toReal/M₂)
  have hFm : ∀ e ∈ S, Measurable (F e) := fun e _ =>
    distanceBinIntegrand_measurable ρ ν _ _ M₁ M₂ b₁ b₂ h₁ h₂ _ _ _
  have hCb : ∀ e ∈ S, ∀ p, ‖F e p‖ ≤ C e := fun e _ p =>
    distanceBinIntegrand_bound ρ ν _ _ hM₁ hM₂ b₁ b₂ hB₁ hB₂ hb₁ hb₂ _ _ _ p
  have hh := finite_angular_square_radial S F hFm C (fun e _ => by dsimp [C]; positivity)
    hCb hΨ hs hW hw (by positivity : 0 < (2:ℝ)^v)
  rw [sourceRadialSquareEnergy_complex a v hΨ hpos (fun t ht => by
    by_contra hn
    have := (hs t hn).1
    linarith)]
  simp_rw [sourceParentRetainedF_bin_sum N sig t X Y ρ ν n hM₁ hM₂ b₁ b₂ h₁ h₂ hB₁ hB₂ hb₁ hb₂]
  change ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
    (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • ((‖∑ e ∈ S, ∫ u, F e (r,u) ∂sourceArcLength‖^2 : ℝ) : ℂ))) = _
  rw [hh]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  simp only [F, sourceParentBinIntegrand, distanceBinIntegrand_cross, sourceParentGraphTerm, graphOriginalTerm]

theorem sourceParentGraphTerm_profile_ratios (N : ℕ) (sig t v : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hp₁ : Mp₁ ≠ 0) (hp₂ : Mp₂ ≠ 0)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (Ψ : ℝ → ℝ) (e f : ParentDistanceBinLabel) :
    sourceParentGraphTerm N sig t v X Y ρ ν Ma₁ Ma₂ b₁ b₂ Ψ e f =
      ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) • sourceParentGraphTerm N sig t v X Y ρ ν Mp₁ Mp₂ b₁ b₂ Ψ e f := by
  unfold sourceParentGraphTerm
  rw [graphOriginalTerm_profile_normalization _ _ ![Mp₁,Mp₂,Mp₂,Mp₁] ![Ma₁,Ma₂,Ma₂,Ma₁]
    (by intro index; fin_cases index <;> first | exact hp₁ | exact hp₂)]
  congr 1
  change (Mp₁/Ma₁)*(Mp₂/Ma₂)*(Mp₂/Ma₂)*(Mp₁/Ma₁) = (Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2
  ring

end PlanarFalconer

end OAI

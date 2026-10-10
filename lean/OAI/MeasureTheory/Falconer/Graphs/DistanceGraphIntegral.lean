import OAI.MeasureTheory.Falconer.Graphs.DistanceGraphPointwise
import OAI.MeasureTheory.Falconer.Measures.DistanceSchurIntegral
import OAI.MeasureTheory.Falconer.Graphs.ProductGraphEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem original_distance_graph_integral_bound
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (N a n : ℕ) (sig t : ℝ) (hA : A.length = a) (hB : B.length = a)
    {θ : ℝ} (hθ : 0 < θ) (hscale : θ = graphUncappedAngularScale N sig t) (axis : ℝ) (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    {d : ℝ} (hd : 0 ≤ d)
    (hdegree : ∀ j k s reverse row,
      ((activeDistanceMatrixNeighbors I (a+n) j k θ axis s reverse row).card : ℝ) ≤ d)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ B₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ B₂)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    let U := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform ρ (Q₁.descendant P).carrier M₁ β z.1 z.2
    let V := fun Q : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform ν (Q₂.descendant Q).carrier M₂ γ z.1 z.2
    ‖((2:ℝ)^(2*(v-(a+n)))) •
      ∑ e ∈ I, graphOriginalTerm ![ρ,ν,ν,ρ]
        (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier)
        ![M₁,M₂,M₂,M₁] ![β,γ,γ,β] true e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ‖ ≤
      d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (sourceAngularH (a+n) v Ψ (U row.1) (V row.2)).toReal := by
  classical
  let : ∀ l : Fin 4, IsFiniteMeasure (![ρ,ν,ν,ρ] l) := by
    intro l; fin_cases l <;> dsimp <;> infer_instance
  have hM : ∀ l : Fin 4, 0 < (![M₁,M₂,M₂,M₁] l) := by
    intro l; fin_cases l <;> first | exact hM₁ | exact hM₂
  have hb : ∀ l : Fin 4, Measurable (fun z : Plane × UnitCircle => (![β,γ,γ,β] l) z.1 z.2) := by
    intro l; fin_cases l <;> first | exact hβ | exact hγ
  have hbound : ∀ (l : Fin 4) x u, ‖(![β,γ,γ,β] l) x u‖ ≤ (![B₁,B₂,B₂,B₁] l) := by
    intro l; fin_cases l <;> first | exact hbβ | exact hbγ
  have hB4 : ∀ l : Fin 4, 0 ≤ (![B₁,B₂,B₂,B₁] l) := by
    intro l; fin_cases l <;> first | exact hB₁ | exact hB₂
  let H := graphSupportedDistanceIndices I θ axis
  let F := fun z : ℝ × (UnitCircle × UnitCircle) => ∑ e ∈ H,
    sourceGraphFourTransform ![ρ,ν,ν,ρ]
      (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier)
      ![M₁,M₂,M₂,M₁] ![β,γ,γ,β]
      (graphRotatedDistanceWeight axis (angularBinCount θ) e.2.1.1 e.2.1.2) z.1 z.2.1 z.2.2
  let U := fun P : CellPath => fun z : ℝ × UnitCircle =>
    sourceAngularTransform ρ (Q₁.descendant P).carrier M₁ β z.1 z.2
  let V := fun Q : CellPath => fun z : ℝ × UnitCircle =>
    sourceAngularTransform ν (Q₂.descendant Q).carrier M₂ γ z.1 z.2
  have hpoint (r : ℝ) (u w : UnitCircle) : ‖F (r,(u,w))‖ ≤
      d/2 * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (‖U row.1 (r,u)‖^2*‖V row.2 (r,w)‖^2 + ‖V row.2 (r,u)‖^2*‖U row.1 (r,w)‖^2) :=
    distance_graph_pointwise_bound Q₁ Q₂ ρ ν A B N a n sig t hA hB
      I hI hθ hscale axis d hd hdegree (fun P u => U P (r,u)) (fun Q w => V Q (r,w)) u w
  have hmain := original_distance_schur_integral (sourceProductVertices Q₁ Q₂ ρ ν A B n)
    (fun row => U row.1) (fun row => V row.2)
    (fun row _ => measurable_sourceAngularTransform ρ (Q₁.descendant row.1).carrier M₁ β hβ)
    (fun row _ => measurable_sourceAngularTransform ν (Q₂.descendant row.2).carrier M₂ γ hγ)
    (fun row => B₁*(ρ (Q₁.descendant row.1).carrier).toReal/M₁)
    (fun row => B₂*(ν (Q₂.descendant row.2).carrier).toReal/M₂)
    (fun row _ => by positivity) (fun row _ => by positivity)
    (fun row _ z => sourceAngularTransform_norm_le ρ _ M₁ hM₁ β B₁ (fun x _ => hbβ x) z.1 z.2)
    (fun row _ z => sourceAngularTransform_norm_le ν _ M₂ hM₂ γ B₂ (fun x _ => hbγ x) z.1 z.2)
    F hd hpoint (a+n) v hΨ hpos hs hW hw
  have hsum := sourceGraphFourTransform_original_sum H ![ρ,ν,ν,ρ]
    (fun e l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier)
    ![M₁,M₂,M₂,M₁] hM ![β,γ,γ,β]
    (fun e => graphRotatedDistanceWeight axis (angularBinCount θ) e.2.1.1 e.2.1.2) hb
    (fun e => (graphRotatedDistanceWeight_continuous _ _ _ _).measurable)
    (fun e => graphRotatedDistanceWeight_norm_le _ _ _ _)
    ![B₁,B₂,B₂,B₁] hB4 hbound hΨ hs hW
    (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t) v
  dsimp only [F] at hmain
  rw [hsum] at hmain
  dsimp only
  rw [graphOriginalDistanceSum_supported]
  simpa only [Finset.smul_sum,graphOriginalTerm,graphSourceWeight,
    ↓reduceIte,H,U,V] using hmain

end PlanarFalconer

end OAI

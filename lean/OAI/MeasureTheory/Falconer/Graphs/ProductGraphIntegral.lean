import OAI.MeasureTheory.Falconer.Graphs.ProductGraphPointwise
import OAI.MeasureTheory.Falconer.Measures.ProductSchurIntegral
import OAI.MeasureTheory.Falconer.Graphs.ProductGraphEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem original_product_graph_integral_bound
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a)
    {θ : ℝ} (hθ : 0 < θ) (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ) A B)
    {d : ℝ} (hd : 0 ≤ d)
    (hdegree : ∀ j k s reverse row,
      ((activeProductMatrixNeighbors I (a+n) j k θ s reverse row).card : ℝ) ≤ d)
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
      ∑ e ∈ I, graphOriginalTerm ![ρ,ρ,ν,ν]
        (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
        ![M₁,M₁,M₂,M₂] ![β,β,γ,γ] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ‖ ≤
      d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (sourceAngularH (a+n) v Ψ (U row.1) (V row.2)).toReal := by
  classical
  let : ∀ l : Fin 4, IsFiniteMeasure (![ρ,ρ,ν,ν] l) := by
    intro l; fin_cases l <;> dsimp <;> infer_instance
  have hM : ∀ l : Fin 4, 0 < (![M₁,M₁,M₂,M₂] l) := by
    intro l; fin_cases l <;> first | exact hM₁ | exact hM₂
  have hb : ∀ l : Fin 4, Measurable (fun z : Plane × UnitCircle => (![β,β,γ,γ] l) z.1 z.2) := by
    intro l; fin_cases l <;> first | exact hβ | exact hγ
  have hbound : ∀ (l : Fin 4) x u, ‖(![β,β,γ,γ] l) x u‖ ≤ (![B₁,B₁,B₂,B₂] l) := by
    intro l; fin_cases l <;> first | exact hbβ | exact hbγ
  have hB4 : ∀ l : Fin 4, 0 ≤ (![B₁,B₁,B₂,B₂] l) := by
    intro l; fin_cases l <;> first | exact hB₁ | exact hB₂
  let H := graphSupportedProductIndices I θ
  let F := fun z : ℝ × (UnitCircle × UnitCircle) => ∑ e ∈ H,
    sourceGraphFourTransform ![ρ,ρ,ν,ν]
      (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
      ![M₁,M₁,M₂,M₂] ![β,β,γ,γ]
      (graphProductWeight e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2) z.1 z.2.1 z.2.2
  let U := fun P : CellPath => fun z : ℝ × UnitCircle =>
    sourceAngularTransform ρ (Q₁.descendant P).carrier M₁ β z.1 z.2
  let V := fun Q : CellPath => fun z : ℝ × UnitCircle =>
    sourceAngularTransform ν (Q₂.descendant Q).carrier M₂ γ z.1 z.2
  have hpoint (r : ℝ) (u w : UnitCircle) : ‖F (r,(u,w))‖ ≤
      d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, ‖U row.1 (r,u)‖^2*‖V row.2 (r,w)‖^2 :=
    product_graph_pointwise_bound Q₁ Q₂ ρ ν A B a n (angularBinCount θ) hA hB
      (angularBinCount_pos hθ) I hI θ d hdegree (fun P => U P (r,u)) (fun Q => V Q (r,w)) u w
  have hmain := original_product_schur_integral (sourceProductVertices Q₁ Q₂ ρ ν A B n)
    (fun row => U row.1) (fun row => V row.2)
    (fun row _ => measurable_sourceAngularTransform ρ (Q₁.descendant row.1).carrier M₁ β hβ)
    (fun row _ => measurable_sourceAngularTransform ν (Q₂.descendant row.2).carrier M₂ γ hγ)
    (fun row => B₁*(ρ (Q₁.descendant row.1).carrier).toReal/M₁)
    (fun row => B₂*(ν (Q₂.descendant row.2).carrier).toReal/M₂)
    (fun row _ => by positivity) (fun row _ => by positivity)
    (fun row _ z => sourceAngularTransform_norm_le ρ _ M₁ hM₁ β B₁ (fun x _ => hbβ x) z.1 z.2)
    (fun row _ z => sourceAngularTransform_norm_le ν _ M₂ hM₂ γ B₂ (fun x _ => hbγ x) z.1 z.2)
    F hd hpoint (a+n) v hΨ hpos hs hW hw
  have hsum := sourceGraphFourTransform_original_sum H ![ρ,ρ,ν,ν]
    (fun e l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
    ![M₁,M₁,M₂,M₂] hM ![β,β,γ,γ]
    (fun e => graphProductWeight e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2) hb
    (fun e => (graphProductWeight_continuous _ _ _ _).measurable)
    (fun e => graphProductWeight_norm_le _ _ _ _)
    ![B₁,B₁,B₂,B₂] hB4 hbound hΨ hs hW
    (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t) v
  dsimp only [F] at hmain
  rw [hsum] at hmain
  dsimp only
  rw [graphOriginalProductSum_supported]
  simpa only [Finset.smul_sum,graphOriginalTerm,graphSourceWeight,
    Bool.false_eq_true,↓reduceIte,H,U,V] using hmain

end PlanarFalconer

end OAI

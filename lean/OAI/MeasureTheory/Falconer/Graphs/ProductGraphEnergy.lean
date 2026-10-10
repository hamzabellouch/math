import OAI.MeasureTheory.Falconer.Estimates.ProductTransformPartition
import OAI.MeasureTheory.Falconer.Measures.FiniteProductIntegral
import OAI.MeasureTheory.Falconer.Angular.AngularProductEnergyIntegral
import OAI.MeasureTheory.Falconer.Graphs.GraphOriginalNonedgePower

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceGraphFourTransform_original_sum {ι : Type*} (S : Finset ι)
    (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (X : ι → Fin 4 → Set Plane) (M : Fin 4 → ℝ) (hM : ∀ l, 0 < M l)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : ι → UnitCircle × UnitCircle → ℂ)
    (hb : ∀ l, Measurable (fun p : Plane × UnitCircle => b l p.1 p.2))
    (hW : ∀ i, Measurable (W i)) (hw : ∀ i p, ‖W i p‖ ≤ 1)
    (B : Fin 4 → ℝ) (hB : ∀ l, 0 ≤ B l) (hbound : ∀ l x dir, ‖b l x dir‖ ≤ B l)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) (v : ℝ) :
    (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
      (∑ i ∈ S, sourceGraphFourTransform ρ (X i) M b (W i) r u w)
      ∂sourceArcLength ∂sourceArcLength) =
    ∑ i ∈ S, ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
      sourceGraphFourTransform ρ (X i) M b (W i) r u w ∂sourceArcLength ∂sourceArcLength := by
  apply bounded_original_integral_sum S _
    (fun i _ => sourceGraphFourTransform_measurable ρ (X i) M b (W i) hb (hW i))
    (fun i => ((B 0*(ρ 0 (X i 0)).toReal/M 0)*(B 1*(ρ 1 (X i 1)).toReal/M 1))*
      ((B 2*(ρ 2 (X i 2)).toReal/M 2)*(B 3*(ρ 3 (X i 3)).toReal/M 3)))
    (fun i _ => by
      have h0 := hB 0; have h1 := hB 1; have h2 := hB 2; have h3 := hB 3
      have hm0 := hM 0; have hm1 := hM 1; have hm2 := hM 2; have hm3 := hM 3
      positivity)
    (fun i _ p => sourceGraphFourTransform_bound ρ (X i) M hM b (W i) B hB hbound (hw i) p.1 p.2.1 p.2.2)
    hΨ hs hC hc (by positivity)

theorem sourceAngularH_relative_graph_sum (a v : ℝ)
    (X Y : DyadicSquare) (hX : 0 < X.side) (hY : 0 < Y.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ) {θ : ℝ} (hθ : 0 < θ)
    {Ma₁ Ma₂ Mp₁ Mp₂ : ℝ} (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hb₁ : Measurable (fun p : Plane × UnitCircle => b₁ p.1 p.2))
    (hb₂ : Measurable (fun p : Plane × UnitCircle => b₂ p.1 p.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hbound₂ : ∀ x dir, ‖b₂ x dir‖ ≤ B₂)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) :
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform ρ X.carrier Ma₁ b₁ z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform ν Y.carrier Ma₂ b₂ z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) =
      ((2:ℝ)^(2*(v-a))) • (((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
        ∑ e ∈ sourceProductRelativeIndices X Y ρ ν n (angularBinCount θ),
          graphOriginalTerm ![ρ,ρ,ν,ν] (fun l => (graphQuadCells ![X,X,Y,Y] e.1 l).carrier)
            ![Mp₁,Mp₁,Mp₂,Mp₂] ![b₁,b₁,b₂,b₂] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ) := by
  classical
  let : ∀ l : Fin 4, IsFiniteMeasure (![ρ,ρ,ν,ν] l) := by
    intro l; fin_cases l <;> dsimp <;> infer_instance
  have hM : ∀ l : Fin 4, 0 < (![Mp₁,Mp₁,Mp₂,Mp₂] l) := by
    intro l; fin_cases l <;> first | exact hMp₁ | exact hMp₂
  have hb : ∀ l : Fin 4, Measurable (fun p : Plane × UnitCircle => (![b₁,b₁,b₂,b₂] l) p.1 p.2) := by
    intro l; fin_cases l <;> first | exact hb₁ | exact hb₂
  have hB : ∀ l : Fin 4, 0 ≤ (![B₁,B₁,B₂,B₂] l) := by
    intro l; fin_cases l <;> first | exact hB₁ | exact hB₂
  have hbound : ∀ (l : Fin 4) x dir, ‖(![b₁,b₁,b₂,b₂] l) x dir‖ ≤ (![B₁,B₁,B₂,B₂] l) := by
    intro l; fin_cases l <;> first | exact hbound₁ | exact hbound₂
  obtain ⟨hfin,he⟩ := sourceAngularH_original_four_transform a v hΨ hpos hs hC
    (fun t => (le_abs_self _).trans (hc t)) ρ ν X.carrier Y.carrier hMa₁ hMa₂ b₁ b₂ hb₁ hb₂
    hB₁ hB₂ hbound₁ hbound₂
  refine ⟨hfin,?_⟩
  rw [he]
  have hp (r : ℝ) (u w : UnitCircle) :
      sourceGraphFourTransform ![ρ,ρ,ν,ν] ![X.carrier,X.carrier,Y.carrier,Y.carrier]
        ![Ma₁,Ma₁,Ma₂,Ma₂] ![b₁,b₁,b₂,b₂] (fun _ => 1) r u w =
      ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
        ∑ e ∈ sourceProductRelativeIndices X Y ρ ν n (angularBinCount θ),
          sourceGraphFourTransform ![ρ,ρ,ν,ν] (fun l => (graphQuadCells ![X,X,Y,Y] e.1 l).carrier)
            ![Mp₁,Mp₁,Mp₂,Mp₂] ![b₁,b₁,b₂,b₂]
            (graphProductWeight e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2) r u w := by
    rw [sourceGraphFourTransform_profile_normalization _ _ ![Mp₁,Mp₁,Mp₂,Mp₂] _ (fun l => ne_of_gt (hM l))]
    rw [sourceGraphFourTransform_product_partition X Y hX hY ρ ν n (angularBinCount θ)
      (angularBinCount_pos hθ) Mp₁ Mp₂ hMp₁.ne' hMp₂.ne' b₁ b₂ hb₁ hb₂ B₁ B₂ hbound₁ hbound₂]
    congr 1
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons]
    ring
  simp_rw [hp,smul_comm (Ψ _) ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2),integral_smul]
  have hsum := sourceGraphFourTransform_original_sum
    (sourceProductRelativeIndices X Y ρ ν n (angularBinCount θ)) ![ρ,ρ,ν,ν]
    (fun e l => (graphQuadCells ![X,X,Y,Y] e.1 l).carrier) ![Mp₁,Mp₁,Mp₂,Mp₂] hM
    ![b₁,b₁,b₂,b₂]
    (fun e => graphProductWeight e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2) hb
    (fun e => (graphProductWeight_continuous e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2).measurable)
    (fun e => graphProductWeight_norm_le e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2)
    ![B₁,B₁,B₂,B₂] hB hbound hΨ hs hC hc v
  simp only [integral_smul] at hsum
  rw [hsum]
  simp only [graphOriginalTerm,graphSourceWeight,Bool.false_eq_true,↓reduceIte,integral_smul,← Finset.smul_sum]
  rw [smul_comm (((2:ℝ)^v)⁻¹)]

end PlanarFalconer

end OAI
